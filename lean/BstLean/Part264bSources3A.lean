import BstLean.Part264bUniformFull
import BstLean.Part264bUniformEnergy
import BstLean.Part264bSourceCommon
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
import BstLean.Part264FiniteCentre
import BstLean.Part264HS
import BstLean.Part264Source
namespace BstLean.Part264b.N12300
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12300 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12300 12300 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12300.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12300 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12300 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12300 := gPlus_lower 12300
end BstLean.Part264b.N12300

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12300
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036391988638 : ℝ) ≤ wn 12300 := by
  have hn : √(12300 : ℝ) ≤ 110.905365064095 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12300 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.905365064095 ≤ 2 / √12300 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260218439 : ℝ) ≤ rhoBar 12300 BstLean.Part154.csC ∧
    rhoBar 12300 BstLean.Part154.csC ≤ 0.000260247217 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036391988638 : ℝ) / (1.295212 * 12300) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12300) := by gcongr
      _ ≤ (0.000260247217 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12300 BstLean.Part154.csC) ≤ 0.001041056597 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12300 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12300 BstLean.Part154.csC) (piBar (rhoBar 12300 BstLean.Part154.csC)) ≤ 0.000198778887 ∧
    cc1 (rhoBar 12300 BstLean.Part154.csC) (piBar (rhoBar 12300 BstLean.Part154.csC)) ≤ 0.000126484262 ∧
    cc2 (rhoBar 12300 BstLean.Part154.csC) ≤ 0.000073425007 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12300 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12300 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12300 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12300 BstLean.Part154.csC * nuR (rhoBar 12300 BstLean.Part154.csC)) ≤ 0.000520511366 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260247217 : ℝ) * 0.001041056597 := by gcongr
      _ ≤ (0.000520511366 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12300 BstLean.Part154.csC) * nuR (rhoBar 12300 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041056597 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12300 BstLean.Part154.csC) * rhoBar 12300 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260247217 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260247217 / 2 + 0.399 * 0.001041056597 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198778887 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520511366 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126484262 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260247217 / 1.414213562 := by gcongr
      _ ≤ (0.000073425007 : ℝ) := by norm_num

end BstLean.Part264b.N12300

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12300
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12300 BstLean.Part154.csC) (piBar (rhoBar 12300 BstLean.Part154.csC)) ≤ 1.70638E-7 := by
  have hr0 : 0 ≤ rhoBar 12300 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12300 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12300 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12300 BstLean.Part154.csC) (piBar (rhoBar 12300 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12300 BstLean.Part154.csC) (piBar (rhoBar 12300 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12300 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198778887 : ℝ) ^ 2 + 0.000126484262 ^ 2 + 3 * 0.000073425007 ^ 2 +
        2 * 0.797885 * 0.000198778887 * 0.000126484262 + 2 * 0.000198778887 * 0.000073425007 +
        4 * 0.797885 * 0.000126484262 * 0.000073425007 := by gcongr
    _ ≤ (1.70638E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12300 BstLean.Part154.csC Θ ≤ 0.002718748770 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12300 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12300 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12300 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12300 BstLean.Part154.csC) (piBar (rhoBar 12300 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12300 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70638E-7 / (0.000260218439 : ℝ) := by gcongr
    _ ≤ 0.002718748770 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12300 BstLean.Part154.csC Θ ≤ 0.003018291324 + 0.000686906618 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12300 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12300 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12300 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260247217 +
        (6863 / 10000) * 0.000260247217 * 12300 * 0.001041056597) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003018291324 + 0.000686906618 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12300 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12300 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12300 0.011 Θ ∧ gammaRatio 12300 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12300 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12300) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12300 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12300 0.011 Θ) :=
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
    badAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12300 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12300 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12300 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12300 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12300 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12300 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12300 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12300 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12300 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12300 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12300 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004118291324 + 0.003405655388 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12300

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12300
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12300 BstLean.Part154.csC) (piBar (rhoBar 12300 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12300 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12300 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12300 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12300 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12300 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12300 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12300 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12300 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12300 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12300 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12300 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12300 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053340216480 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12300) ≤ 0.010768077635 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12300 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010768077635 + 2 * 0.737676 / 12300) := by gcongr
    _ ≤ (0.053340216480 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12300 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12300

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12300
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484890837 : ℝ) ≤ plow 12300 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12300) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412860403)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427343105) : eMP 12300 0.011 xi bn ≤ 0.001228073024 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12300 : ℝ) * (1 - 0.011))) ≤ 0.000607139446 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001427343105 / (12300 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607139446 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607139446 : ℝ) + 3.141593 * 0.053412860403 / (12300 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001228073024 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412860403)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427343105) : PiBarMP 12300 12 0.011 xi bn ≤ 0.163886458348 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12300 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037780194614 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.293698822734 : ℝ) ≤ √((12300 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.905365064094 : ℝ) ≤ √12300 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12300) ≤ 0.125624294684 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037780194614 + 0.053412860403 * 1.772454 / (2 * (110.293698822734 : ℝ))) * (1 + 0.001228073024) +
        8 / (12300 * 110.905365064094) + 0.125624294684 := by gcongr
    _ ≤ (0.163886458348 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412860403)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427343105) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284452441174) :
    parallelOracle 12300 0.011 xi bn cd ≤ 0.164912274719 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12300 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12300 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484890837 : ℝ) ≤ plow 12300 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.905365064094 : ℝ) ≤ √12300 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284452441174 : ℝ) / (2 * 0.560484890837 * 110.905365064094)) * 0.163886458348 +
        0.284452441174 ^ 2 / (2 * 0.560484890837 * 110.905365064094) := by gcongr
    _ ≤ (0.164912274719 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412860403) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427343105)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284452441174) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12300 12300 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484890837 : ℝ) ≤ plow 12300 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.905365064094 : ℝ) ≤ √12300 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12300 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12300 Θ 1.22 ≤ 0.011957045534 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.905365064094 := by gcongr <;> linarith
      _ ≤ (0.011957045534 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12300 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12300 12300 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12300 12300 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12300 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12300 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12300 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12300 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164912274719 + 0.011957045534 + (0.008646 : ℝ) *
        (1 + 2 * (0.284452441174 + 0.011957045534) / (0.560484890837 * 110.905365064094))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12300]

end BstLean.Part264b.N12300

/-! The original eight local profiles supply actual 12300 moment certificates. -/
namespace BstLean.Part264b.N12300
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12300 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053412860403 ∧
    0 ≤ bN 12300 BstLean.Part154.csC (groupTheta g) ∧ bN 12300 BstLean.Part154.csC (groupTheta g) ≤ 0.001427343105 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12300 12300 0.011
      (momentAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12300 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12300 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12300 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231112224694 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12300 0.011
      (momentAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12300 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12300
/-! The actual computed-centre upper energy formula at 12300. -/
namespace BstLean.Part264b.N12300
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12300

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12300
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12300 cell12300)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086756888913
  | 2 => 0.087725337819
  | 3 => 0.088696052102
  | 4 => 0.089671369237
  | 5 => 0.090654080768
  | 6 => 0.091647494928
  | 7 => 0.092655504299
  | 8 => 0.093682658414
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12300 12300 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12300 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12300

/-! Actual upper energy certificates on all 43 source endpoints at 12300. -/
namespace BstLean.Part264b.N12300
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12300 cell12300)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12300 (gMinus 12300) (1 - (cell12300 i).lower) ≤ 1 ∧
    energyUpper 12300 (gMinus 12300) (BstLean.Part211.gPlus 12300)
      (finiteEnergy 12300 12300 0.011) (1 - (cell12300 i).lower) ≤
      (cell12300 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12300) (by norm_num)
        (q := 1 - (cell12300 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12300,cell12300]) (by norm_num [scalarRow12300,cell12300])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12300,cell12300])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12300

/-! Source-cell containment and simple scalar guards at 12300. -/
namespace BstLean.Part264b.N12300
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12300 cell12300)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12300 ⟨10,by decide⟩).lower ∧ (cell12300 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12300 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12300 ⟨11,by decide⟩).lower ∧ (cell12300 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12300 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12300 ⟨12,by decide⟩).lower ∧ (cell12300 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12300 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12300 ⟨13,by decide⟩).lower ∧ (cell12300 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12300 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12300 ⟨14,by decide⟩).lower ∧ (cell12300 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12300 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12300 ⟨15,by decide⟩).lower ∧ (cell12300 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12300 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12300 ⟨16,by decide⟩).lower ∧ (cell12300 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12300 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12300 ⟨17,by decide⟩).lower ∧ (cell12300 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12300 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12300 ⟨18,by decide⟩).lower ∧ (cell12300 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12300 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12300 ⟨19,by decide⟩).lower ∧ (cell12300 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12300 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12300 ⟨20,by decide⟩).lower ∧ (cell12300 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12300 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12300 ⟨21,by decide⟩).lower ∧ (cell12300 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12300 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12300 ⟨22,by decide⟩).lower ∧ (cell12300 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12300 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12300 ⟨23,by decide⟩).lower ∧ (cell12300 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12300 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12300 ⟨24,by decide⟩).lower ∧ (cell12300 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12300 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12300 ⟨25,by decide⟩).lower ∧ (cell12300 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12300 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12300 ⟨26,by decide⟩).lower ∧ (cell12300 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12300 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12300 ⟨27,by decide⟩).lower ∧ (cell12300 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12300 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12300 ⟨28,by decide⟩).lower ∧ (cell12300 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12300 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12300 ⟨29,by decide⟩).lower ∧ (cell12300 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12300 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12300 ⟨30,by decide⟩).lower ∧ (cell12300 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12300 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12300 ⟨31,by decide⟩).lower ∧ (cell12300 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12300 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12300 ⟨32,by decide⟩).lower ∧ (cell12300 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12300 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12300 ⟨33,by decide⟩).lower ∧ (cell12300 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12300 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12300 ⟨34,by decide⟩).lower ∧ (cell12300 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12300 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12300 ⟨35,by decide⟩).lower ∧ (cell12300 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12300 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12300 ⟨36,by decide⟩).lower ∧ (cell12300 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12300 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12300 ⟨37,by decide⟩).lower ∧ (cell12300 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12300 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12300 ⟨38,by decide⟩).lower ∧ (cell12300 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12300 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12300 ⟨39,by decide⟩).lower ∧ (cell12300 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12300 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12300 ⟨40,by decide⟩).lower ∧ (cell12300 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12300 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12300 ⟨41,by decide⟩).lower ∧ (cell12300 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12300 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12300 ⟨42,by decide⟩).lower ∧ (cell12300 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12300 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12300 ⟨43,by decide⟩).lower ∧ (cell12300 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12300 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12300 ⟨44,by decide⟩).lower ∧ (cell12300 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12300 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12300 ⟨45,by decide⟩).lower ∧ (cell12300 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12300 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12300 ⟨46,by decide⟩).lower ∧ (cell12300 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12300 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12300 ⟨47,by decide⟩).lower ∧ (cell12300 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12300 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12300 ⟨48,by decide⟩).lower ∧ (cell12300 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12300 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12300 ⟨49,by decide⟩).lower ∧ (cell12300 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12300 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12300 ⟨50,by decide⟩).lower ∧ (cell12300 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12300 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12300 ⟨51,by decide⟩).lower ∧ (cell12300 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12300 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12300 ⟨52,by decide⟩).lower ∧ (cell12300 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12300 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12300 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12300 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12300,cell12300,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12300 i).lower ∧
    (cell12300 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12300 i).upper ≤ (0.532 : ℝ) ∧
    (cell12300 i).centre ≤ (0.1 : ℝ) ∧ (cell12300 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12300 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12300 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12300

/-! The local source numeric instances at 12300 have no network premises. -/
namespace BstLean.Part264b.N12300
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12300 cell12300)

noncomputable def sourceNumerics12300 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12300 (cell12300 i)
      scalarRow12300.M scalarRow12300.H scalarRow12300.xi := by
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
    energy_allowance := scalarRow12300.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12300]
    centre_nonneg := (scalarRow12300.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12300]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12300
/-! Actual 12301 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12301
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12301 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12301 12301 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12301.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12301 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12301 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12301 := gPlus_lower 12301
end BstLean.Part264b.N12301

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12301
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036390496161 : ℝ) ≤ wn 12301 := by
  have hn : √(12301 : ℝ) ≤ 110.909873320639 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12301 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.909873320639 ≤ 2 / √12301 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260196910 : ℝ) ≤ rhoBar 12301 BstLean.Part154.csC ∧
    rhoBar 12301 BstLean.Part154.csC ≤ 0.000260226060 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036390496161 : ℝ) / (1.295212 * 12301) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12301) := by gcongr
      _ ≤ (0.000260226060 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12301 BstLean.Part154.csC) ≤ 0.001040971958 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12301 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12301 BstLean.Part154.csC) (piBar (rhoBar 12301 BstLean.Part154.csC)) ≤ 0.000198762726 ∧
    cc1 (rhoBar 12301 BstLean.Part154.csC) (piBar (rhoBar 12301 BstLean.Part154.csC)) ≤ 0.000126473980 ∧
    cc2 (rhoBar 12301 BstLean.Part154.csC) ≤ 0.000073419038 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12301 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12301 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12301 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12301 BstLean.Part154.csC * nuR (rhoBar 12301 BstLean.Part154.csC)) ≤ 0.000520469050 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260226060 : ℝ) * 0.001040971958 := by gcongr
      _ ≤ (0.000520469050 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12301 BstLean.Part154.csC) * nuR (rhoBar 12301 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040971958 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12301 BstLean.Part154.csC) * rhoBar 12301 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260226060 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260226060 / 2 + 0.399 * 0.001040971958 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198762726 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520469050 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126473980 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260226060 / 1.414213562 := by gcongr
      _ ≤ (0.000073419038 : ℝ) := by norm_num

end BstLean.Part264b.N12301

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12301
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12301 BstLean.Part154.csC) (piBar (rhoBar 12301 BstLean.Part154.csC)) ≤ 1.70610E-7 := by
  have hr0 : 0 ≤ rhoBar 12301 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12301 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12301 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12301 BstLean.Part154.csC) (piBar (rhoBar 12301 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12301 BstLean.Part154.csC) (piBar (rhoBar 12301 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12301 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198762726 : ℝ) ^ 2 + 0.000126473980 ^ 2 + 3 * 0.000073419038 ^ 2 +
        2 * 0.797885 * 0.000198762726 * 0.000126473980 + 2 * 0.000198762726 * 0.000073419038 +
        4 * 0.797885 * 0.000126473980 * 0.000073419038 := by gcongr
    _ ≤ (1.70610E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12301 BstLean.Part154.csC Θ ≤ 0.002718527566 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12301 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12301 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12301 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12301 BstLean.Part154.csC) (piBar (rhoBar 12301 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12301 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70610E-7 / (0.000260196910 : ℝ) := by gcongr
    _ ≤ 0.002718527566 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12301 BstLean.Part154.csC Θ ≤ 0.003018045929 + 0.000686850775 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12301 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12301 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12301 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260226060 +
        (6863 / 10000) * 0.000260226060 * 12301 * 0.001040971958) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003018045929 + 0.000686850775 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12301 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12301 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12301 0.011 Θ ∧ gammaRatio 12301 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12301 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12301) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12301 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12301 0.011 Θ) :=
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
    badAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12301 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12301 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12301 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12301 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12301 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12301 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12301 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12301 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12301 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12301 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12301 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004118045929 + 0.003405378341 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12301

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12301
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12301 BstLean.Part154.csC) (piBar (rhoBar 12301 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12301 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12301 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12301 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12301 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12301 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12301 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12301 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12301 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12301 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12301 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12301 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12301 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053338024427 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12301) ≤ 0.010767639935 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12301 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010767639935 + 2 * 0.737676 / 12301) := by gcongr
    _ ≤ (0.053338024427 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12301 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12301

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12301
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484939045 : ℝ) ≤ plow 12301 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12301) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412469559)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427226973) : eMP 12301 0.011 xi bn ≤ 0.001227973045 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12301 : ℝ) * (1 - 0.011))) ≤ 0.000607090068 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001427226973 / (12301 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607090068 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607090068 : ℝ) + 3.141593 * 0.053412469559 / (12301 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001227973045 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412469559)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427226973) : PiBarMP 12301 12 0.011 xi bn ≤ 0.163879787972 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12301 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037778657639 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.298182215302 : ℝ) ≤ √((12301 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.909873320638 : ℝ) ≤ √12301 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12301) ≤ 0.125619188316 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037778657639 + 0.053412469559 * 1.772454 / (2 * (110.298182215302 : ℝ))) * (1 + 0.001227973045) +
        8 / (12301 * 110.909873320638) + 0.125619188316 := by gcongr
    _ ≤ (0.163879787972 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412469559)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427226973) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284449403548) :
    parallelOracle 12301 0.011 xi bn cd ≤ 0.164905529393 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12301 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12301 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484939045 : ℝ) ≤ plow 12301 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.909873320638 : ℝ) ≤ √12301 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284449403548 : ℝ) / (2 * 0.560484939045 * 110.909873320638)) * 0.163879787972 +
        0.284449403548 ^ 2 / (2 * 0.560484939045 * 110.909873320638) := by gcongr
    _ ≤ (0.164905529393 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412469559) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427226973)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284449403548) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12301 12301 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484939045 : ℝ) ≤ plow 12301 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.909873320638 : ℝ) ≤ √12301 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12301 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12301 Θ 1.22 ≤ 0.011956559505 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.909873320638 := by gcongr <;> linarith
      _ ≤ (0.011956559505 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12301 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12301 12301 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12301 12301 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12301 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12301 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12301 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12301 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164905529393 + 0.011956559505 + (0.008646 : ℝ) *
        (1 + 2 * (0.284449403548 + 0.011956559505) / (0.560484939045 * 110.909873320638))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12301]

end BstLean.Part264b.N12301

/-! The original eight local profiles supply actual 12301 moment certificates. -/
namespace BstLean.Part264b.N12301
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12301 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053412469559 ∧
    0 ≤ bN 12301 BstLean.Part154.csC (groupTheta g) ∧ bN 12301 BstLean.Part154.csC (groupTheta g) ≤ 0.001427226973 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12301 12301 0.011
      (momentAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12301 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12301 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12301 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231111379121 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12301 0.011
      (momentAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12301 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12301
/-! The actual computed-centre upper energy formula at 12301. -/
namespace BstLean.Part264b.N12301
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12301

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12301
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12301 cell12301)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086753434669
  | 2 => 0.087721806660
  | 3 => 0.088692430762
  | 4 => 0.089667641575
  | 5 => 0.090650227291
  | 6 => 0.091643492260
  | 7 => 0.092651324598
  | 8 => 0.093678268728
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12301 12301 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12301 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12301

/-! Actual upper energy certificates on all 43 source endpoints at 12301. -/
namespace BstLean.Part264b.N12301
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12301 cell12301)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12301 (gMinus 12301) (1 - (cell12301 i).lower) ≤ 1 ∧
    energyUpper 12301 (gMinus 12301) (BstLean.Part211.gPlus 12301)
      (finiteEnergy 12301 12301 0.011) (1 - (cell12301 i).lower) ≤
      (cell12301 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12301) (by norm_num)
        (q := 1 - (cell12301 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12301,cell12301]) (by norm_num [scalarRow12301,cell12301])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12301,cell12301])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12301

/-! Source-cell containment and simple scalar guards at 12301. -/
namespace BstLean.Part264b.N12301
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12301 cell12301)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12301 ⟨10,by decide⟩).lower ∧ (cell12301 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12301 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12301 ⟨11,by decide⟩).lower ∧ (cell12301 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12301 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12301 ⟨12,by decide⟩).lower ∧ (cell12301 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12301 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12301 ⟨13,by decide⟩).lower ∧ (cell12301 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12301 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12301 ⟨14,by decide⟩).lower ∧ (cell12301 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12301 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12301 ⟨15,by decide⟩).lower ∧ (cell12301 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12301 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12301 ⟨16,by decide⟩).lower ∧ (cell12301 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12301 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12301 ⟨17,by decide⟩).lower ∧ (cell12301 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12301 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12301 ⟨18,by decide⟩).lower ∧ (cell12301 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12301 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12301 ⟨19,by decide⟩).lower ∧ (cell12301 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12301 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12301 ⟨20,by decide⟩).lower ∧ (cell12301 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12301 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12301 ⟨21,by decide⟩).lower ∧ (cell12301 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12301 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12301 ⟨22,by decide⟩).lower ∧ (cell12301 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12301 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12301 ⟨23,by decide⟩).lower ∧ (cell12301 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12301 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12301 ⟨24,by decide⟩).lower ∧ (cell12301 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12301 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12301 ⟨25,by decide⟩).lower ∧ (cell12301 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12301 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12301 ⟨26,by decide⟩).lower ∧ (cell12301 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12301 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12301 ⟨27,by decide⟩).lower ∧ (cell12301 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12301 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12301 ⟨28,by decide⟩).lower ∧ (cell12301 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12301 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12301 ⟨29,by decide⟩).lower ∧ (cell12301 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12301 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12301 ⟨30,by decide⟩).lower ∧ (cell12301 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12301 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12301 ⟨31,by decide⟩).lower ∧ (cell12301 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12301 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12301 ⟨32,by decide⟩).lower ∧ (cell12301 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12301 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12301 ⟨33,by decide⟩).lower ∧ (cell12301 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12301 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12301 ⟨34,by decide⟩).lower ∧ (cell12301 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12301 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12301 ⟨35,by decide⟩).lower ∧ (cell12301 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12301 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12301 ⟨36,by decide⟩).lower ∧ (cell12301 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12301 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12301 ⟨37,by decide⟩).lower ∧ (cell12301 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12301 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12301 ⟨38,by decide⟩).lower ∧ (cell12301 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12301 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12301 ⟨39,by decide⟩).lower ∧ (cell12301 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12301 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12301 ⟨40,by decide⟩).lower ∧ (cell12301 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12301 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12301 ⟨41,by decide⟩).lower ∧ (cell12301 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12301 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12301 ⟨42,by decide⟩).lower ∧ (cell12301 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12301 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12301 ⟨43,by decide⟩).lower ∧ (cell12301 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12301 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12301 ⟨44,by decide⟩).lower ∧ (cell12301 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12301 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12301 ⟨45,by decide⟩).lower ∧ (cell12301 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12301 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12301 ⟨46,by decide⟩).lower ∧ (cell12301 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12301 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12301 ⟨47,by decide⟩).lower ∧ (cell12301 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12301 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12301 ⟨48,by decide⟩).lower ∧ (cell12301 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12301 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12301 ⟨49,by decide⟩).lower ∧ (cell12301 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12301 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12301 ⟨50,by decide⟩).lower ∧ (cell12301 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12301 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12301 ⟨51,by decide⟩).lower ∧ (cell12301 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12301 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12301 ⟨52,by decide⟩).lower ∧ (cell12301 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12301 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12301 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12301 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12301,cell12301,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12301 i).lower ∧
    (cell12301 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12301 i).upper ≤ (0.532 : ℝ) ∧
    (cell12301 i).centre ≤ (0.1 : ℝ) ∧ (cell12301 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12301 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12301 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12301

/-! The local source numeric instances at 12301 have no network premises. -/
namespace BstLean.Part264b.N12301
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12301 cell12301)

noncomputable def sourceNumerics12301 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12301 (cell12301 i)
      scalarRow12301.M scalarRow12301.H scalarRow12301.xi := by
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
    energy_allowance := scalarRow12301.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12301]
    centre_nonneg := (scalarRow12301.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12301]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12301
/-! Actual 12302 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12302
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12302 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12302 12302 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12302.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12302 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12302 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12302 := gPlus_lower 12302
end BstLean.Part264b.N12302

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12302
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036389003867 : ℝ) ≤ wn 12302 := by
  have hn : √(12302 : ℝ) ≤ 110.914381393939 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12302 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.914381393939 ≤ 2 / √12302 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260175384 : ℝ) ≤ rhoBar 12302 BstLean.Part154.csC ∧
    rhoBar 12302 BstLean.Part154.csC ≤ 0.000260204907 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036389003867 : ℝ) / (1.295212 * 12302) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12302) := by gcongr
      _ ≤ (0.000260204907 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12302 BstLean.Part154.csC) ≤ 0.001040887335 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12302 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12302 BstLean.Part154.csC) (piBar (rhoBar 12302 BstLean.Part154.csC)) ≤ 0.000198746569 ∧
    cc1 (rhoBar 12302 BstLean.Part154.csC) (piBar (rhoBar 12302 BstLean.Part154.csC)) ≤ 0.000126463699 ∧
    cc2 (rhoBar 12302 BstLean.Part154.csC) ≤ 0.000073413070 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12302 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12302 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12302 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12302 BstLean.Part154.csC * nuR (rhoBar 12302 BstLean.Part154.csC)) ≤ 0.000520426741 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260204907 : ℝ) * 0.001040887335 := by gcongr
      _ ≤ (0.000520426741 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12302 BstLean.Part154.csC) * nuR (rhoBar 12302 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040887335 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12302 BstLean.Part154.csC) * rhoBar 12302 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260204907 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260204907 / 2 + 0.399 * 0.001040887335 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198746569 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520426741 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126463699 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260204907 / 1.414213562 := by gcongr
      _ ≤ (0.000073413070 : ℝ) := by norm_num

end BstLean.Part264b.N12302

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12302
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12302 BstLean.Part154.csC) (piBar (rhoBar 12302 BstLean.Part154.csC)) ≤ 1.70582E-7 := by
  have hr0 : 0 ≤ rhoBar 12302 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12302 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12302 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12302 BstLean.Part154.csC) (piBar (rhoBar 12302 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12302 BstLean.Part154.csC) (piBar (rhoBar 12302 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12302 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198746569 : ℝ) ^ 2 + 0.000126463699 ^ 2 + 3 * 0.000073413070 ^ 2 +
        2 * 0.797885 * 0.000198746569 * 0.000126463699 + 2 * 0.000198746569 * 0.000073413070 +
        4 * 0.797885 * 0.000126463699 * 0.000073413070 := by gcongr
    _ ≤ (1.70582E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12302 BstLean.Part154.csC Θ ≤ 0.002718306294 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12302 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12302 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12302 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12302 BstLean.Part154.csC) (piBar (rhoBar 12302 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12302 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70582E-7 / (0.000260175384 : ℝ) := by gcongr
    _ ≤ 0.002718306294 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12302 BstLean.Part154.csC Θ ≤ 0.003017800587 + 0.000686794943 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12302 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12302 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12302 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260204907 +
        (6863 / 10000) * 0.000260204907 * 12302 * 0.001040887335) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003017800587 + 0.000686794943 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12302 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12302 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12302 0.011 Θ ∧ gammaRatio 12302 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12302 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12302) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12302 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12302 0.011 Θ) :=
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
    badAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12302 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12302 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12302 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12302 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12302 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12302 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12302 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12302 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12302 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12302 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12302 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004117800587 + 0.003405101237 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12302

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12302
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12302 BstLean.Part154.csC) (piBar (rhoBar 12302 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12302 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12302 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12302 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12302 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12302 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12302 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12302 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12302 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12302 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12302 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12302 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12302 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053335832640 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12302) ≤ 0.010767202288 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12302 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010767202288 + 2 * 0.737676 / 12302) := by gcongr
    _ ≤ (0.053335832640 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12302 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12302

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12302
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484987245 : ℝ) ≤ plow 12302 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12302) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412078737)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427110805) : eMP 12302 0.011 xi bn ≤ 0.001227873061 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12302 : ℝ) * (1 - 0.011))) ≤ 0.000607040687 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001427110805 / (12302 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607040687 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607040687 : ℝ) + 3.141593 * 0.053412078737 / (12302 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001227873061 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412078737)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427110805) : PiBarMP 12302 12 0.011 xi bn ≤ 0.163873117684 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12302 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037777120126 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.302665425636 : ℝ) ≤ √((12302 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.914381393938 : ℝ) ≤ √12302 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12302) ≤ 0.125614082572 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037777120126 + 0.053412078737 * 1.772454 / (2 * (110.302665425636 : ℝ))) * (1 + 0.001227873061) +
        8 / (12302 * 110.914381393938) + 0.125614082572 := by gcongr
    _ ≤ (0.163873117684 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412078737)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427110805) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284446366232) :
    parallelOracle 12302 0.011 xi bn cd ≤ 0.164898784164 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12302 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12302 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484987245 : ℝ) ≤ plow 12302 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.914381393938 : ℝ) ≤ √12302 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284446366232 : ℝ) / (2 * 0.560484987245 * 110.914381393938)) * 0.163873117684 +
        0.284446366232 ^ 2 / (2 * 0.560484987245 * 110.914381393938) := by gcongr
    _ ≤ (0.164898784164 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053412078737) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427110805)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284446366232) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12302 12302 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484987245 : ℝ) ≤ plow 12302 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.914381393938 : ℝ) ≤ √12302 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12302 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12302 Θ 1.22 ≤ 0.011956073535 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.914381393938 := by gcongr <;> linarith
      _ ≤ (0.011956073535 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12302 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12302 12302 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12302 12302 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12302 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12302 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12302 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12302 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164898784164 + 0.011956073535 + (0.008646 : ℝ) *
        (1 + 2 * (0.284446366232 + 0.011956073535) / (0.560484987245 * 110.914381393938))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12302]

end BstLean.Part264b.N12302

/-! The original eight local profiles supply actual 12302 moment certificates. -/
namespace BstLean.Part264b.N12302
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12302 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053412078737 ∧
    0 ≤ bN 12302 BstLean.Part154.csC (groupTheta g) ∧ bN 12302 BstLean.Part154.csC (groupTheta g) ≤ 0.001427110805 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12302 12302 0.011
      (momentAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12302 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12302 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12302 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231110533592 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12302 0.011
      (momentAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12302 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12302
/-! The actual computed-centre upper energy formula at 12302. -/
namespace BstLean.Part264b.N12302
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12302

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12302
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12302 cell12302)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086749982082
  | 2 => 0.087718277233
  | 3 => 0.088688811247
  | 4 => 0.089663915851
  | 5 => 0.090646375889
  | 6 => 0.091639491834
  | 7 => 0.092647147339
  | 8 => 0.093673881725
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12302 12302 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12302 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12302

/-! Actual upper energy certificates on all 43 source endpoints at 12302. -/
namespace BstLean.Part264b.N12302
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12302 cell12302)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12302 (gMinus 12302) (1 - (cell12302 i).lower) ≤ 1 ∧
    energyUpper 12302 (gMinus 12302) (BstLean.Part211.gPlus 12302)
      (finiteEnergy 12302 12302 0.011) (1 - (cell12302 i).lower) ≤
      (cell12302 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12302) (by norm_num)
        (q := 1 - (cell12302 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12302,cell12302]) (by norm_num [scalarRow12302,cell12302])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12302,cell12302])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12302

/-! Source-cell containment and simple scalar guards at 12302. -/
namespace BstLean.Part264b.N12302
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12302 cell12302)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12302 ⟨10,by decide⟩).lower ∧ (cell12302 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12302 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12302 ⟨11,by decide⟩).lower ∧ (cell12302 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12302 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12302 ⟨12,by decide⟩).lower ∧ (cell12302 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12302 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12302 ⟨13,by decide⟩).lower ∧ (cell12302 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12302 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12302 ⟨14,by decide⟩).lower ∧ (cell12302 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12302 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12302 ⟨15,by decide⟩).lower ∧ (cell12302 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12302 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12302 ⟨16,by decide⟩).lower ∧ (cell12302 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12302 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12302 ⟨17,by decide⟩).lower ∧ (cell12302 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12302 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12302 ⟨18,by decide⟩).lower ∧ (cell12302 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12302 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12302 ⟨19,by decide⟩).lower ∧ (cell12302 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12302 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12302 ⟨20,by decide⟩).lower ∧ (cell12302 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12302 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12302 ⟨21,by decide⟩).lower ∧ (cell12302 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12302 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12302 ⟨22,by decide⟩).lower ∧ (cell12302 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12302 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12302 ⟨23,by decide⟩).lower ∧ (cell12302 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12302 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12302 ⟨24,by decide⟩).lower ∧ (cell12302 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12302 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12302 ⟨25,by decide⟩).lower ∧ (cell12302 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12302 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12302 ⟨26,by decide⟩).lower ∧ (cell12302 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12302 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12302 ⟨27,by decide⟩).lower ∧ (cell12302 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12302 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12302 ⟨28,by decide⟩).lower ∧ (cell12302 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12302 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12302 ⟨29,by decide⟩).lower ∧ (cell12302 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12302 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12302 ⟨30,by decide⟩).lower ∧ (cell12302 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12302 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12302 ⟨31,by decide⟩).lower ∧ (cell12302 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12302 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12302 ⟨32,by decide⟩).lower ∧ (cell12302 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12302 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12302 ⟨33,by decide⟩).lower ∧ (cell12302 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12302 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12302 ⟨34,by decide⟩).lower ∧ (cell12302 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12302 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12302 ⟨35,by decide⟩).lower ∧ (cell12302 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12302 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12302 ⟨36,by decide⟩).lower ∧ (cell12302 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12302 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12302 ⟨37,by decide⟩).lower ∧ (cell12302 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12302 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12302 ⟨38,by decide⟩).lower ∧ (cell12302 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12302 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12302 ⟨39,by decide⟩).lower ∧ (cell12302 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12302 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12302 ⟨40,by decide⟩).lower ∧ (cell12302 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12302 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12302 ⟨41,by decide⟩).lower ∧ (cell12302 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12302 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12302 ⟨42,by decide⟩).lower ∧ (cell12302 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12302 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12302 ⟨43,by decide⟩).lower ∧ (cell12302 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12302 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12302 ⟨44,by decide⟩).lower ∧ (cell12302 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12302 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12302 ⟨45,by decide⟩).lower ∧ (cell12302 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12302 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12302 ⟨46,by decide⟩).lower ∧ (cell12302 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12302 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12302 ⟨47,by decide⟩).lower ∧ (cell12302 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12302 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12302 ⟨48,by decide⟩).lower ∧ (cell12302 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12302 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12302 ⟨49,by decide⟩).lower ∧ (cell12302 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12302 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12302 ⟨50,by decide⟩).lower ∧ (cell12302 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12302 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12302 ⟨51,by decide⟩).lower ∧ (cell12302 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12302 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12302 ⟨52,by decide⟩).lower ∧ (cell12302 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12302 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12302 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12302 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12302,cell12302,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12302 i).lower ∧
    (cell12302 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12302 i).upper ≤ (0.532 : ℝ) ∧
    (cell12302 i).centre ≤ (0.1 : ℝ) ∧ (cell12302 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12302 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12302 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12302

/-! The local source numeric instances at 12302 have no network premises. -/
namespace BstLean.Part264b.N12302
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12302 cell12302)

noncomputable def sourceNumerics12302 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12302 (cell12302 i)
      scalarRow12302.M scalarRow12302.H scalarRow12302.xi := by
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
    energy_allowance := scalarRow12302.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12302]
    centre_nonneg := (scalarRow12302.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12302]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12302
/-! Actual 12303 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12303
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12303 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12303 12303 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12303.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12303 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12303 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12303 := gPlus_lower 12303
end BstLean.Part264b.N12303

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12303
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036387511756 : ℝ) ≤ wn 12303 := by
  have hn : √(12303 : ℝ) ≤ 110.918889284017 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12303 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.918889284017 ≤ 2 / √12303 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260153862 : ℝ) ≤ rhoBar 12303 BstLean.Part154.csC ∧
    rhoBar 12303 BstLean.Part154.csC ≤ 0.000260183757 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036387511756 : ℝ) / (1.295212 * 12303) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12303) := by gcongr
      _ ≤ (0.000260183757 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12303 BstLean.Part154.csC) ≤ 0.001040802724 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12303 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12303 BstLean.Part154.csC) (piBar (rhoBar 12303 BstLean.Part154.csC)) ≤ 0.000198730414 ∧
    cc1 (rhoBar 12303 BstLean.Part154.csC) (piBar (rhoBar 12303 BstLean.Part154.csC)) ≤ 0.000126453419 ∧
    cc2 (rhoBar 12303 BstLean.Part154.csC) ≤ 0.000073407102 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12303 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12303 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12303 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12303 BstLean.Part154.csC * nuR (rhoBar 12303 BstLean.Part154.csC)) ≤ 0.000520384438 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260183757 : ℝ) * 0.001040802724 := by gcongr
      _ ≤ (0.000520384438 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12303 BstLean.Part154.csC) * nuR (rhoBar 12303 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040802724 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12303 BstLean.Part154.csC) * rhoBar 12303 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260183757 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260183757 / 2 + 0.399 * 0.001040802724 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198730414 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520384438 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126453419 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260183757 / 1.414213562 := by gcongr
      _ ≤ (0.000073407102 : ℝ) := by norm_num

end BstLean.Part264b.N12303

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12303
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12303 BstLean.Part154.csC) (piBar (rhoBar 12303 BstLean.Part154.csC)) ≤ 1.70555E-7 := by
  have hr0 : 0 ≤ rhoBar 12303 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12303 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12303 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12303 BstLean.Part154.csC) (piBar (rhoBar 12303 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12303 BstLean.Part154.csC) (piBar (rhoBar 12303 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12303 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198730414 : ℝ) ^ 2 + 0.000126453419 ^ 2 + 3 * 0.000073407102 ^ 2 +
        2 * 0.797885 * 0.000198730414 * 0.000126453419 + 2 * 0.000198730414 * 0.000073407102 +
        4 * 0.797885 * 0.000126453419 * 0.000073407102 := by gcongr
    _ ≤ (1.70555E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12303 BstLean.Part154.csC Θ ≤ 0.002718100880 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12303 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12303 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12303 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12303 BstLean.Part154.csC) (piBar (rhoBar 12303 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12303 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70555E-7 / (0.000260153862 : ℝ) := by gcongr
    _ ≤ 0.002718100880 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12303 BstLean.Part154.csC Θ ≤ 0.003017555275 + 0.000686739119 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12303 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12303 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12303 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260183757 +
        (6863 / 10000) * 0.000260183757 * 12303 * 0.001040802724) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003017555275 + 0.000686739119 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12303 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12303 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12303 0.011 Θ ∧ gammaRatio 12303 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12303 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12303) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12303 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12303 0.011 Θ) :=
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
    badAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12303 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12303 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12303 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12303 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12303 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12303 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12303 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12303 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12303 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12303 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12303 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004117555275 + 0.003404839999 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12303

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12303
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12303 BstLean.Part154.csC) (piBar (rhoBar 12303 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12303 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12303 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12303 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12303 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12303 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12303 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12303 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12303 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12303 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12303 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12303 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12303 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053333641127 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12303) ≤ 0.010766764695 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12303 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010766764695 + 2 * 0.737676 / 12303) := by gcongr
    _ ≤ (0.053333641127 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12303 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12303

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12303
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485035438 : ℝ) ≤ plow 12303 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12303) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053411696275)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427002962) : eMP 12303 0.011 xi bn ≤ 0.001227776628 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12303 : ℝ) * (1 - 0.011))) ≤ 0.000606993080 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001427002962 / (12303 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606993080 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606993080 : ℝ) + 3.141593 * 0.053411696275 / (12303 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001227776628 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053411696275)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427002962) : PiBarMP 12303 12 0.011 xi bn ≤ 0.163866558486 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12303 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037775692741 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.307148453760 : ℝ) ≤ √((12303 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.918889284016 : ℝ) ≤ √12303 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12303) ≤ 0.125608977450 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037775692741 + 0.053411696275 * 1.772454 / (2 * (110.307148453760 : ℝ))) * (1 + 0.001227776628) +
        8 / (12303 * 110.918889284016) + 0.125608977450 := by gcongr
    _ ≤ (0.163866558486 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053411696275)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427002962) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284443347274) :
    parallelOracle 12303 0.011 xi bn cd ≤ 0.164892150396 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12303 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12303 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485035438 : ℝ) ≤ plow 12303 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.918889284016 : ℝ) ≤ √12303 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284443347274 : ℝ) / (2 * 0.560485035438 * 110.918889284016)) * 0.163866558486 +
        0.284443347274 ^ 2 / (2 * 0.560485035438 * 110.918889284016) := by gcongr
    _ ≤ (0.164892150396 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053411696275) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427002962)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284443347274) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12303 12303 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485035438 : ℝ) ≤ plow 12303 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.918889284016 : ℝ) ≤ √12303 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12303 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12303 Θ 1.22 ≤ 0.011955587625 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.918889284016 := by gcongr <;> linarith
      _ ≤ (0.011955587625 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12303 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12303 12303 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12303 12303 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12303 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12303 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12303 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12303 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164892150396 + 0.011955587625 + (0.008646 : ℝ) *
        (1 + 2 * (0.284443347274 + 0.011955587625) / (0.560485035438 * 110.918889284016))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12303]

end BstLean.Part264b.N12303

/-! The original eight local profiles supply actual 12303 moment certificates. -/
namespace BstLean.Part264b.N12303
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12303 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053411696275 ∧
    0 ≤ bN 12303 BstLean.Part154.csC (groupTheta g) ∧ bN 12303 BstLean.Part154.csC (groupTheta g) ≤ 0.001427002962 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12303 12303 0.011
      (momentAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12303 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12303 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12303 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231109706147 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12303 0.011
      (momentAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12303 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12303
/-! The actual computed-centre upper energy formula at 12303. -/
namespace BstLean.Part264b.N12303
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12303

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12303
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12303 cell12303)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086746531152
  | 2 => 0.087714749537
  | 3 => 0.088685193556
  | 4 => 0.089660192064
  | 5 => 0.090642526562
  | 6 => 0.091635493649
  | 7 => 0.092642972521
  | 8 => 0.093669497401
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12303 12303 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12303 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12303

/-! Actual upper energy certificates on all 43 source endpoints at 12303. -/
namespace BstLean.Part264b.N12303
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12303 cell12303)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12303 (gMinus 12303) (1 - (cell12303 i).lower) ≤ 1 ∧
    energyUpper 12303 (gMinus 12303) (BstLean.Part211.gPlus 12303)
      (finiteEnergy 12303 12303 0.011) (1 - (cell12303 i).lower) ≤
      (cell12303 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12303) (by norm_num)
        (q := 1 - (cell12303 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12303,cell12303]) (by norm_num [scalarRow12303,cell12303])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12303,cell12303])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12303

/-! Source-cell containment and simple scalar guards at 12303. -/
namespace BstLean.Part264b.N12303
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12303 cell12303)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12303 ⟨10,by decide⟩).lower ∧ (cell12303 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12303 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12303 ⟨11,by decide⟩).lower ∧ (cell12303 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12303 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12303 ⟨12,by decide⟩).lower ∧ (cell12303 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12303 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12303 ⟨13,by decide⟩).lower ∧ (cell12303 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12303 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12303 ⟨14,by decide⟩).lower ∧ (cell12303 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12303 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12303 ⟨15,by decide⟩).lower ∧ (cell12303 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12303 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12303 ⟨16,by decide⟩).lower ∧ (cell12303 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12303 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12303 ⟨17,by decide⟩).lower ∧ (cell12303 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12303 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12303 ⟨18,by decide⟩).lower ∧ (cell12303 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12303 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12303 ⟨19,by decide⟩).lower ∧ (cell12303 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12303 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12303 ⟨20,by decide⟩).lower ∧ (cell12303 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12303 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12303 ⟨21,by decide⟩).lower ∧ (cell12303 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12303 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12303 ⟨22,by decide⟩).lower ∧ (cell12303 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12303 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12303 ⟨23,by decide⟩).lower ∧ (cell12303 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12303 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12303 ⟨24,by decide⟩).lower ∧ (cell12303 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12303 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12303 ⟨25,by decide⟩).lower ∧ (cell12303 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12303 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12303 ⟨26,by decide⟩).lower ∧ (cell12303 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12303 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12303 ⟨27,by decide⟩).lower ∧ (cell12303 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12303 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12303 ⟨28,by decide⟩).lower ∧ (cell12303 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12303 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12303 ⟨29,by decide⟩).lower ∧ (cell12303 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12303 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12303 ⟨30,by decide⟩).lower ∧ (cell12303 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12303 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12303 ⟨31,by decide⟩).lower ∧ (cell12303 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12303 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12303 ⟨32,by decide⟩).lower ∧ (cell12303 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12303 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12303 ⟨33,by decide⟩).lower ∧ (cell12303 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12303 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12303 ⟨34,by decide⟩).lower ∧ (cell12303 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12303 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12303 ⟨35,by decide⟩).lower ∧ (cell12303 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12303 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12303 ⟨36,by decide⟩).lower ∧ (cell12303 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12303 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12303 ⟨37,by decide⟩).lower ∧ (cell12303 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12303 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12303 ⟨38,by decide⟩).lower ∧ (cell12303 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12303 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12303 ⟨39,by decide⟩).lower ∧ (cell12303 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12303 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12303 ⟨40,by decide⟩).lower ∧ (cell12303 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12303 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12303 ⟨41,by decide⟩).lower ∧ (cell12303 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12303 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12303 ⟨42,by decide⟩).lower ∧ (cell12303 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12303 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12303 ⟨43,by decide⟩).lower ∧ (cell12303 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12303 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12303 ⟨44,by decide⟩).lower ∧ (cell12303 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12303 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12303 ⟨45,by decide⟩).lower ∧ (cell12303 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12303 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12303 ⟨46,by decide⟩).lower ∧ (cell12303 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12303 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12303 ⟨47,by decide⟩).lower ∧ (cell12303 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12303 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12303 ⟨48,by decide⟩).lower ∧ (cell12303 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12303 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12303 ⟨49,by decide⟩).lower ∧ (cell12303 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12303 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12303 ⟨50,by decide⟩).lower ∧ (cell12303 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12303 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12303 ⟨51,by decide⟩).lower ∧ (cell12303 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12303 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12303 ⟨52,by decide⟩).lower ∧ (cell12303 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12303 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12303 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12303 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12303,cell12303,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12303 i).lower ∧
    (cell12303 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12303 i).upper ≤ (0.532 : ℝ) ∧
    (cell12303 i).centre ≤ (0.1 : ℝ) ∧ (cell12303 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12303 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12303 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12303

/-! The local source numeric instances at 12303 have no network premises. -/
namespace BstLean.Part264b.N12303
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12303 cell12303)

noncomputable def sourceNumerics12303 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12303 (cell12303 i)
      scalarRow12303.M scalarRow12303.H scalarRow12303.xi := by
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
    energy_allowance := scalarRow12303.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12303]
    centre_nonneg := (scalarRow12303.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12303]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12303
/-! Actual 12304 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12304
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12304 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12304 12304 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12304.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12304 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12304 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12304 := gPlus_lower 12304
end BstLean.Part264b.N12304

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12304
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036386019827 : ℝ) ≤ wn 12304 := by
  have hn : √(12304 : ℝ) ≤ 110.923396990897 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12304 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.923396990897 ≤ 2 / √12304 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260132344 : ℝ) ≤ rhoBar 12304 BstLean.Part154.csC ∧
    rhoBar 12304 BstLean.Part154.csC ≤ 0.000260162611 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036386019827 : ℝ) / (1.295212 * 12304) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12304) := by gcongr
      _ ≤ (0.000260162611 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12304 BstLean.Part154.csC) ≤ 0.001040718129 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12304 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12304 BstLean.Part154.csC) (piBar (rhoBar 12304 BstLean.Part154.csC)) ≤ 0.000198714261 ∧
    cc1 (rhoBar 12304 BstLean.Part154.csC) (piBar (rhoBar 12304 BstLean.Part154.csC)) ≤ 0.000126443141 ∧
    cc2 (rhoBar 12304 BstLean.Part154.csC) ≤ 0.000073401136 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12304 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12304 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12304 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12304 BstLean.Part154.csC * nuR (rhoBar 12304 BstLean.Part154.csC)) ≤ 0.000520342143 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260162611 : ℝ) * 0.001040718129 := by gcongr
      _ ≤ (0.000520342143 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12304 BstLean.Part154.csC) * nuR (rhoBar 12304 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040718129 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12304 BstLean.Part154.csC) * rhoBar 12304 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260162611 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260162611 / 2 + 0.399 * 0.001040718129 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198714261 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520342143 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126443141 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260162611 / 1.414213562 := by gcongr
      _ ≤ (0.000073401136 : ℝ) := by norm_num

end BstLean.Part264b.N12304

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12304
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12304 BstLean.Part154.csC) (piBar (rhoBar 12304 BstLean.Part154.csC)) ≤ 1.70527E-7 := by
  have hr0 : 0 ≤ rhoBar 12304 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12304 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12304 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12304 BstLean.Part154.csC) (piBar (rhoBar 12304 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12304 BstLean.Part154.csC) (piBar (rhoBar 12304 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12304 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198714261 : ℝ) ^ 2 + 0.000126443141 ^ 2 + 3 * 0.000073401136 ^ 2 +
        2 * 0.797885 * 0.000198714261 * 0.000126443141 + 2 * 0.000198714261 * 0.000073401136 +
        4 * 0.797885 * 0.000126443141 * 0.000073401136 := by gcongr
    _ ≤ (1.70527E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12304 BstLean.Part154.csC Θ ≤ 0.002717879452 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12304 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12304 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12304 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12304 BstLean.Part154.csC) (piBar (rhoBar 12304 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12304 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70527E-7 / (0.000260132344 : ℝ) := by gcongr
    _ ≤ 0.002717879452 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12304 BstLean.Part154.csC Θ ≤ 0.003017310015 + 0.000686683305 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12304 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12304 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12304 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260162611 +
        (6863 / 10000) * 0.000260162611 * 12304 * 0.001040718129) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003017310015 + 0.000686683305 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12304 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12304 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12304 0.011 Θ ∧ gammaRatio 12304 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12304 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12304) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12304 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12304 0.011 Θ) :=
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
    badAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12304 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12304 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12304 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12304 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12304 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12304 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12304 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12304 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12304 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12304 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12304 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004117310015 + 0.003404562757 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12304

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12304
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12304 BstLean.Part154.csC) (piBar (rhoBar 12304 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12304 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12304 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12304 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12304 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12304 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12304 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12304 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12304 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12304 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12304 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12304 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12304 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053331449880 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12304) ≤ 0.010766327155 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12304 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010766327155 + 2 * 0.737676 / 12304) := by gcongr
    _ ≤ (0.053331449880 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12304 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12304

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12304
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485083623 : ℝ) ≤ plow 12304 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12304) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053411305463)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426886713) : eMP 12304 0.011 xi bn ≤ 0.001227676626 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12304 : ℝ) * (1 - 0.011))) ≤ 0.000606943690 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001426886713 / (12304 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606943690 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606943690 : ℝ) + 3.141593 * 0.053411305463 / (12304 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001227676626 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053411305463)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426886713) : PiBarMP 12304 12 0.011 xi bn ≤ 0.163859888252 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12304 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037774154035 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.311631299695 : ℝ) ≤ √((12304 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.923396990896 : ℝ) ≤ √12304 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12304) ≤ 0.125603872950 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037774154035 + 0.053411305463 * 1.772454 / (2 * (110.311631299695 : ℝ))) * (1 + 0.001227676626) +
        8 / (12304 * 110.923396990896) + 0.125603872950 := by gcongr
    _ ≤ (0.163859888252 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053411305463)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426886713) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284440310513) :
    parallelOracle 12304 0.011 xi bn cd ≤ 0.164885405242 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12304 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12304 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485083623 : ℝ) ≤ plow 12304 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.923396990896 : ℝ) ≤ √12304 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284440310513 : ℝ) / (2 * 0.560485083623 * 110.923396990896)) * 0.163859888252 +
        0.284440310513 ^ 2 / (2 * 0.560485083623 * 110.923396990896) := by gcongr
    _ ≤ (0.164885405242 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053411305463) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426886713)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284440310513) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12304 12304 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485083623 : ℝ) ≤ plow 12304 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.923396990896 : ℝ) ≤ √12304 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12304 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12304 Θ 1.22 ≤ 0.011955101773 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.923396990896 := by gcongr <;> linarith
      _ ≤ (0.011955101773 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12304 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12304 12304 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12304 12304 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12304 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12304 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12304 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12304 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164885405242 + 0.011955101773 + (0.008646 : ℝ) *
        (1 + 2 * (0.284440310513 + 0.011955101773) / (0.560485083623 * 110.923396990896))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12304]

end BstLean.Part264b.N12304

/-! The original eight local profiles supply actual 12304 moment certificates. -/
namespace BstLean.Part264b.N12304
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12304 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053411305463 ∧
    0 ≤ bN 12304 BstLean.Part154.csC (groupTheta g) ∧ bN 12304 BstLean.Part154.csC (groupTheta g) ≤ 0.001426886713 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12304 12304 0.011
      (momentAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12304 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12304 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12304 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231108860633 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12304 0.011
      (momentAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12304 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12304
/-! The actual computed-centre upper energy formula at 12304. -/
namespace BstLean.Part264b.N12304
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12304

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12304
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12304 cell12304)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086743081876
  | 2 => 0.087711223571
  | 3 => 0.088681577685
  | 4 => 0.089656470211
  | 5 => 0.090638679306
  | 6 => 0.091631497701
  | 7 => 0.092638800140
  | 8 => 0.093665115753
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12304 12304 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12304 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12304

/-! Actual upper energy certificates on all 43 source endpoints at 12304. -/
namespace BstLean.Part264b.N12304
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12304 cell12304)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12304 (gMinus 12304) (1 - (cell12304 i).lower) ≤ 1 ∧
    energyUpper 12304 (gMinus 12304) (BstLean.Part211.gPlus 12304)
      (finiteEnergy 12304 12304 0.011) (1 - (cell12304 i).lower) ≤
      (cell12304 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12304) (by norm_num)
        (q := 1 - (cell12304 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12304,cell12304]) (by norm_num [scalarRow12304,cell12304])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12304,cell12304])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12304

/-! Source-cell containment and simple scalar guards at 12304. -/
namespace BstLean.Part264b.N12304
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12304 cell12304)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12304 ⟨10,by decide⟩).lower ∧ (cell12304 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12304 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12304 ⟨11,by decide⟩).lower ∧ (cell12304 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12304 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12304 ⟨12,by decide⟩).lower ∧ (cell12304 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12304 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12304 ⟨13,by decide⟩).lower ∧ (cell12304 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12304 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12304 ⟨14,by decide⟩).lower ∧ (cell12304 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12304 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12304 ⟨15,by decide⟩).lower ∧ (cell12304 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12304 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12304 ⟨16,by decide⟩).lower ∧ (cell12304 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12304 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12304 ⟨17,by decide⟩).lower ∧ (cell12304 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12304 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12304 ⟨18,by decide⟩).lower ∧ (cell12304 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12304 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12304 ⟨19,by decide⟩).lower ∧ (cell12304 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12304 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12304 ⟨20,by decide⟩).lower ∧ (cell12304 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12304 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12304 ⟨21,by decide⟩).lower ∧ (cell12304 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12304 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12304 ⟨22,by decide⟩).lower ∧ (cell12304 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12304 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12304 ⟨23,by decide⟩).lower ∧ (cell12304 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12304 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12304 ⟨24,by decide⟩).lower ∧ (cell12304 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12304 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12304 ⟨25,by decide⟩).lower ∧ (cell12304 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12304 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12304 ⟨26,by decide⟩).lower ∧ (cell12304 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12304 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12304 ⟨27,by decide⟩).lower ∧ (cell12304 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12304 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12304 ⟨28,by decide⟩).lower ∧ (cell12304 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12304 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12304 ⟨29,by decide⟩).lower ∧ (cell12304 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12304 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12304 ⟨30,by decide⟩).lower ∧ (cell12304 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12304 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12304 ⟨31,by decide⟩).lower ∧ (cell12304 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12304 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12304 ⟨32,by decide⟩).lower ∧ (cell12304 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12304 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12304 ⟨33,by decide⟩).lower ∧ (cell12304 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12304 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12304 ⟨34,by decide⟩).lower ∧ (cell12304 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12304 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12304 ⟨35,by decide⟩).lower ∧ (cell12304 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12304 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12304 ⟨36,by decide⟩).lower ∧ (cell12304 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12304 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12304 ⟨37,by decide⟩).lower ∧ (cell12304 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12304 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12304 ⟨38,by decide⟩).lower ∧ (cell12304 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12304 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12304 ⟨39,by decide⟩).lower ∧ (cell12304 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12304 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12304 ⟨40,by decide⟩).lower ∧ (cell12304 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12304 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12304 ⟨41,by decide⟩).lower ∧ (cell12304 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12304 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12304 ⟨42,by decide⟩).lower ∧ (cell12304 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12304 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12304 ⟨43,by decide⟩).lower ∧ (cell12304 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12304 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12304 ⟨44,by decide⟩).lower ∧ (cell12304 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12304 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12304 ⟨45,by decide⟩).lower ∧ (cell12304 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12304 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12304 ⟨46,by decide⟩).lower ∧ (cell12304 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12304 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12304 ⟨47,by decide⟩).lower ∧ (cell12304 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12304 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12304 ⟨48,by decide⟩).lower ∧ (cell12304 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12304 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12304 ⟨49,by decide⟩).lower ∧ (cell12304 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12304 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12304 ⟨50,by decide⟩).lower ∧ (cell12304 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12304 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12304 ⟨51,by decide⟩).lower ∧ (cell12304 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12304 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12304 ⟨52,by decide⟩).lower ∧ (cell12304 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12304 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12304 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12304 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12304,cell12304,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12304 i).lower ∧
    (cell12304 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12304 i).upper ≤ (0.532 : ℝ) ∧
    (cell12304 i).centre ≤ (0.1 : ℝ) ∧ (cell12304 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12304 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12304 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12304

/-! The local source numeric instances at 12304 have no network premises. -/
namespace BstLean.Part264b.N12304
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12304 cell12304)

noncomputable def sourceNumerics12304 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12304 (cell12304 i)
      scalarRow12304.M scalarRow12304.H scalarRow12304.xi := by
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
    energy_allowance := scalarRow12304.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12304]
    centre_nonneg := (scalarRow12304.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12304]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12304
/-! Actual 12305 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12305
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12305 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12305 12305 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12305.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12305 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12305 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12305 := gPlus_lower 12305
end BstLean.Part264b.N12305

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12305
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036384528082 : ℝ) ≤ wn 12305 := by
  have hn : √(12305 : ℝ) ≤ 110.927904514600 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12305 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.927904514600 ≤ 2 / √12305 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260110829 : ℝ) ≤ rhoBar 12305 BstLean.Part154.csC ∧
    rhoBar 12305 BstLean.Part154.csC ≤ 0.000260141468 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036384528082 : ℝ) / (1.295212 * 12305) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12305) := by gcongr
      _ ≤ (0.000260141468 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12305 BstLean.Part154.csC) ≤ 0.001040633546 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12305 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12305 BstLean.Part154.csC) (piBar (rhoBar 12305 BstLean.Part154.csC)) ≤ 0.000198698111 ∧
    cc1 (rhoBar 12305 BstLean.Part154.csC) (piBar (rhoBar 12305 BstLean.Part154.csC)) ≤ 0.000126432865 ∧
    cc2 (rhoBar 12305 BstLean.Part154.csC) ≤ 0.000073395171 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12305 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12305 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12305 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12305 BstLean.Part154.csC * nuR (rhoBar 12305 BstLean.Part154.csC)) ≤ 0.000520299855 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260141468 : ℝ) * 0.001040633546 := by gcongr
      _ ≤ (0.000520299855 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12305 BstLean.Part154.csC) * nuR (rhoBar 12305 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040633546 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12305 BstLean.Part154.csC) * rhoBar 12305 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260141468 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260141468 / 2 + 0.399 * 0.001040633546 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198698111 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520299855 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126432865 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260141468 / 1.414213562 := by gcongr
      _ ≤ (0.000073395171 : ℝ) := by norm_num

end BstLean.Part264b.N12305

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12305
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12305 BstLean.Part154.csC) (piBar (rhoBar 12305 BstLean.Part154.csC)) ≤ 1.70499E-7 := by
  have hr0 : 0 ≤ rhoBar 12305 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12305 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12305 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12305 BstLean.Part154.csC) (piBar (rhoBar 12305 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12305 BstLean.Part154.csC) (piBar (rhoBar 12305 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12305 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198698111 : ℝ) ^ 2 + 0.000126432865 ^ 2 + 3 * 0.000073395171 ^ 2 +
        2 * 0.797885 * 0.000198698111 * 0.000126432865 + 2 * 0.000198698111 * 0.000073395171 +
        4 * 0.797885 * 0.000126432865 * 0.000073395171 := by gcongr
    _ ≤ (1.70499E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12305 BstLean.Part154.csC Θ ≤ 0.002717657957 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12305 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12305 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12305 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12305 BstLean.Part154.csC) (piBar (rhoBar 12305 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12305 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70499E-7 / (0.000260110829 : ℝ) := by gcongr
    _ ≤ 0.002717657957 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12305 BstLean.Part154.csC Θ ≤ 0.003017064785 + 0.000686627500 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12305 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12305 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12305 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260141468 +
        (6863 / 10000) * 0.000260141468 * 12305 * 0.001040633546) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003017064785 + 0.000686627500 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12305 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12305 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12305 0.011 Θ ∧ gammaRatio 12305 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12305 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12305) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12305 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12305 0.011 Θ) :=
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
    badAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12305 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12305 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12305 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12305 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12305 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12305 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12305 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12305 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12305 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12305 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12305 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004117064785 + 0.003404285457 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12305

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12305
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12305 BstLean.Part154.csC) (piBar (rhoBar 12305 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12305 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12305 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12305 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12305 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12305 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12305 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12305 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12305 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12305 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12305 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12305 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12305 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053329258901 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12305) ≤ 0.010765889668 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12305 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010765889668 + 2 * 0.737676 / 12305) := by gcongr
    _ ≤ (0.053329258901 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12305 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12305

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12305
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485131800 : ℝ) ≤ plow 12305 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12305) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410914650)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426770428) : eMP 12305 0.011 xi bn ≤ 0.001227576616 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12305 : ℝ) * (1 - 0.011))) ≤ 0.000606894296 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001426770428 / (12305 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606894296 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606894296 : ℝ) + 3.141593 * 0.053410914650 / (12305 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001227576616 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410914650)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426770428) : PiBarMP 12305 12 0.011 xi bn ≤ 0.163853218103 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12305 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037772614790 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.316113963464 : ℝ) ≤ √((12305 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.927904514599 : ℝ) ≤ √12305 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12305) ≤ 0.125598769072 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037772614790 + 0.053410914650 * 1.772454 / (2 * (110.316113963464 : ℝ))) * (1 + 0.001227576616) +
        8 / (12305 * 110.927904514599) + 0.125598769072 := by gcongr
    _ ≤ (0.163853218103 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410914650)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426770428) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284437274016) :
    parallelOracle 12305 0.011 xi bn cd ≤ 0.164878660182 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12305 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12305 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485131800 : ℝ) ≤ plow 12305 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.927904514599 : ℝ) ≤ √12305 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284437274016 : ℝ) / (2 * 0.560485131800 * 110.927904514599)) * 0.163853218103 +
        0.284437274016 ^ 2 / (2 * 0.560485131800 * 110.927904514599) := by gcongr
    _ ≤ (0.164878660182 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410914650) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426770428)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284437274016) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12305 12305 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485131800 : ℝ) ≤ plow 12305 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.927904514599 : ℝ) ≤ √12305 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12305 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12305 Θ 1.22 ≤ 0.011954615981 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.927904514599 := by gcongr <;> linarith
      _ ≤ (0.011954615981 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12305 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12305 12305 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12305 12305 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12305 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12305 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12305 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12305 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164878660182 + 0.011954615981 + (0.008646 : ℝ) *
        (1 + 2 * (0.284437274016 + 0.011954615981) / (0.560485131800 * 110.927904514599))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12305]

end BstLean.Part264b.N12305

/-! The original eight local profiles supply actual 12305 moment certificates. -/
namespace BstLean.Part264b.N12305
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12305 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053410914650 ∧
    0 ≤ bN 12305 BstLean.Part154.csC (groupTheta g) ∧ bN 12305 BstLean.Part154.csC (groupTheta g) ≤ 0.001426770428 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12305 12305 0.011
      (momentAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12305 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12305 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12305 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231108015115 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12305 0.011
      (momentAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12305 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12305
/-! The actual computed-centre upper energy formula at 12305. -/
namespace BstLean.Part264b.N12305
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12305

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12305
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12305 cell12305)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086739634252
  | 2 => 0.087707699331
  | 3 => 0.088677963634
  | 4 => 0.089652750290
  | 5 => 0.090634834119
  | 6 => 0.091627503988
  | 7 => 0.092634630194
  | 8 => 0.093660736779
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12305 12305 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12305 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12305

/-! Actual upper energy certificates on all 43 source endpoints at 12305. -/
namespace BstLean.Part264b.N12305
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12305 cell12305)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12305 (gMinus 12305) (1 - (cell12305 i).lower) ≤ 1 ∧
    energyUpper 12305 (gMinus 12305) (BstLean.Part211.gPlus 12305)
      (finiteEnergy 12305 12305 0.011) (1 - (cell12305 i).lower) ≤
      (cell12305 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12305) (by norm_num)
        (q := 1 - (cell12305 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12305,cell12305]) (by norm_num [scalarRow12305,cell12305])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12305,cell12305])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12305

/-! Source-cell containment and simple scalar guards at 12305. -/
namespace BstLean.Part264b.N12305
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12305 cell12305)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12305 ⟨10,by decide⟩).lower ∧ (cell12305 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12305 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12305 ⟨11,by decide⟩).lower ∧ (cell12305 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12305 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12305 ⟨12,by decide⟩).lower ∧ (cell12305 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12305 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12305 ⟨13,by decide⟩).lower ∧ (cell12305 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12305 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12305 ⟨14,by decide⟩).lower ∧ (cell12305 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12305 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12305 ⟨15,by decide⟩).lower ∧ (cell12305 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12305 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12305 ⟨16,by decide⟩).lower ∧ (cell12305 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12305 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12305 ⟨17,by decide⟩).lower ∧ (cell12305 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12305 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12305 ⟨18,by decide⟩).lower ∧ (cell12305 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12305 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12305 ⟨19,by decide⟩).lower ∧ (cell12305 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12305 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12305 ⟨20,by decide⟩).lower ∧ (cell12305 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12305 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12305 ⟨21,by decide⟩).lower ∧ (cell12305 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12305 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12305 ⟨22,by decide⟩).lower ∧ (cell12305 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12305 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12305 ⟨23,by decide⟩).lower ∧ (cell12305 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12305 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12305 ⟨24,by decide⟩).lower ∧ (cell12305 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12305 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12305 ⟨25,by decide⟩).lower ∧ (cell12305 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12305 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12305 ⟨26,by decide⟩).lower ∧ (cell12305 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12305 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12305 ⟨27,by decide⟩).lower ∧ (cell12305 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12305 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12305 ⟨28,by decide⟩).lower ∧ (cell12305 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12305 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12305 ⟨29,by decide⟩).lower ∧ (cell12305 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12305 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12305 ⟨30,by decide⟩).lower ∧ (cell12305 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12305 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12305 ⟨31,by decide⟩).lower ∧ (cell12305 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12305 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12305 ⟨32,by decide⟩).lower ∧ (cell12305 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12305 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12305 ⟨33,by decide⟩).lower ∧ (cell12305 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12305 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12305 ⟨34,by decide⟩).lower ∧ (cell12305 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12305 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12305 ⟨35,by decide⟩).lower ∧ (cell12305 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12305 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12305 ⟨36,by decide⟩).lower ∧ (cell12305 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12305 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12305 ⟨37,by decide⟩).lower ∧ (cell12305 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12305 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12305 ⟨38,by decide⟩).lower ∧ (cell12305 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12305 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12305 ⟨39,by decide⟩).lower ∧ (cell12305 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12305 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12305 ⟨40,by decide⟩).lower ∧ (cell12305 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12305 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12305 ⟨41,by decide⟩).lower ∧ (cell12305 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12305 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12305 ⟨42,by decide⟩).lower ∧ (cell12305 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12305 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12305 ⟨43,by decide⟩).lower ∧ (cell12305 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12305 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12305 ⟨44,by decide⟩).lower ∧ (cell12305 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12305 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12305 ⟨45,by decide⟩).lower ∧ (cell12305 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12305 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12305 ⟨46,by decide⟩).lower ∧ (cell12305 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12305 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12305 ⟨47,by decide⟩).lower ∧ (cell12305 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12305 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12305 ⟨48,by decide⟩).lower ∧ (cell12305 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12305 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12305 ⟨49,by decide⟩).lower ∧ (cell12305 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12305 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12305 ⟨50,by decide⟩).lower ∧ (cell12305 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12305 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12305 ⟨51,by decide⟩).lower ∧ (cell12305 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12305 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12305 ⟨52,by decide⟩).lower ∧ (cell12305 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12305 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12305 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12305 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12305,cell12305,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12305 i).lower ∧
    (cell12305 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12305 i).upper ≤ (0.532 : ℝ) ∧
    (cell12305 i).centre ≤ (0.1 : ℝ) ∧ (cell12305 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12305 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12305 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12305

/-! The local source numeric instances at 12305 have no network premises. -/
namespace BstLean.Part264b.N12305
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12305 cell12305)

noncomputable def sourceNumerics12305 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12305 (cell12305 i)
      scalarRow12305.M scalarRow12305.H scalarRow12305.xi := by
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
    energy_allowance := scalarRow12305.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12305]
    centre_nonneg := (scalarRow12305.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12305]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12305
/-! Actual 12306 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12306
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12306 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12306 12306 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12306.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12306 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12306 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12306 := gPlus_lower 12306
end BstLean.Part264b.N12306

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12306
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036383036520 : ℝ) ≤ wn 12306 := by
  have hn : √(12306 : ℝ) ≤ 110.932411855148 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12306 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.932411855148 ≤ 2 / √12306 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260089318 : ℝ) ≤ rhoBar 12306 BstLean.Part154.csC ∧
    rhoBar 12306 BstLean.Part154.csC ≤ 0.000260120329 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036383036520 : ℝ) / (1.295212 * 12306) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12306) := by gcongr
      _ ≤ (0.000260120329 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12306 BstLean.Part154.csC) ≤ 0.001040548979 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12306 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12306 BstLean.Part154.csC) (piBar (rhoBar 12306 BstLean.Part154.csC)) ≤ 0.000198681964 ∧
    cc1 (rhoBar 12306 BstLean.Part154.csC) (piBar (rhoBar 12306 BstLean.Part154.csC)) ≤ 0.000126422591 ∧
    cc2 (rhoBar 12306 BstLean.Part154.csC) ≤ 0.000073389207 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12306 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12306 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12306 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12306 BstLean.Part154.csC * nuR (rhoBar 12306 BstLean.Part154.csC)) ≤ 0.000520257574 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260120329 : ℝ) * 0.001040548979 := by gcongr
      _ ≤ (0.000520257574 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12306 BstLean.Part154.csC) * nuR (rhoBar 12306 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040548979 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12306 BstLean.Part154.csC) * rhoBar 12306 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260120329 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260120329 / 2 + 0.399 * 0.001040548979 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198681964 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520257574 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126422591 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260120329 / 1.414213562 := by gcongr
      _ ≤ (0.000073389207 : ℝ) := by norm_num

end BstLean.Part264b.N12306

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12306
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12306 BstLean.Part154.csC) (piBar (rhoBar 12306 BstLean.Part154.csC)) ≤ 1.70471E-7 := by
  have hr0 : 0 ≤ rhoBar 12306 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12306 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12306 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12306 BstLean.Part154.csC) (piBar (rhoBar 12306 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12306 BstLean.Part154.csC) (piBar (rhoBar 12306 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12306 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198681964 : ℝ) ^ 2 + 0.000126422591 ^ 2 + 3 * 0.000073389207 ^ 2 +
        2 * 0.797885 * 0.000198681964 * 0.000126422591 + 2 * 0.000198681964 * 0.000073389207 +
        4 * 0.797885 * 0.000126422591 * 0.000073389207 := by gcongr
    _ ≤ (1.70471E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12306 BstLean.Part154.csC Θ ≤ 0.002717436383 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12306 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12306 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12306 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12306 BstLean.Part154.csC) (piBar (rhoBar 12306 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12306 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70471E-7 / (0.000260089318 : ℝ) := by gcongr
    _ ≤ 0.002717436383 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12306 BstLean.Part154.csC Θ ≤ 0.003016819608 + 0.000686571705 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12306 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12306 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12306 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260120329 +
        (6863 / 10000) * 0.000260120329 * 12306 * 0.001040548979) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003016819608 + 0.000686571705 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12306 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12306 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12306 0.011 Θ ∧ gammaRatio 12306 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12306 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12306) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12306 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12306 0.011 Θ) :=
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
    badAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12306 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12306 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12306 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12306 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12306 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12306 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12306 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12306 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12306 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12306 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12306 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004116819608 + 0.003404008088 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12306

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12306
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12306 BstLean.Part154.csC) (piBar (rhoBar 12306 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12306 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12306 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12306 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12306 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12306 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12306 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12306 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12306 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12306 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12306 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12306 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12306 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053327068194 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12306) ≤ 0.010765452235 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12306 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010765452235 + 2 * 0.737676 / 12306) := by gcongr
    _ ≤ (0.053327068194 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12306 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12306

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12306
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485179969 : ℝ) ≤ plow 12306 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12306) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410523855)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426654102) : eMP 12306 0.011 xi bn ≤ 0.001227476597 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12306 : ℝ) * (1 - 0.011))) ≤ 0.000606844897 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001426654102 / (12306 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606844897 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606844897 : ℝ) + 3.141593 * 0.053410523855 / (12306 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001227476597 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410523855)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426654102) : PiBarMP 12306 12 0.011 xi bn ≤ 0.163846547973 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12306 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037771074939 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.320596445088 : ℝ) ≤ √((12306 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.932411855147 : ℝ) ≤ √12306 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12306) ≤ 0.125593665817 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037771074939 + 0.053410523855 * 1.772454 / (2 * (110.320596445088 : ℝ))) * (1 + 0.001227476597) +
        8 / (12306 * 110.932411855147) + 0.125593665817 := by gcongr
    _ ≤ (0.163846547973 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410523855)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426654102) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284434237826) :
    parallelOracle 12306 0.011 xi bn cd ≤ 0.164871915152 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12306 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12306 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485179969 : ℝ) ≤ plow 12306 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.932411855147 : ℝ) ≤ √12306 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284434237826 : ℝ) / (2 * 0.560485179969 * 110.932411855147)) * 0.163846547973 +
        0.284434237826 ^ 2 / (2 * 0.560485179969 * 110.932411855147) := by gcongr
    _ ≤ (0.164871915152 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410523855) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426654102)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284434237826) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12306 12306 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485179969 : ℝ) ≤ plow 12306 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.932411855147 : ℝ) ≤ √12306 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12306 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12306 Θ 1.22 ≤ 0.011954130248 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.932411855147 := by gcongr <;> linarith
      _ ≤ (0.011954130248 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12306 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12306 12306 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12306 12306 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12306 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12306 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12306 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12306 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164871915152 + 0.011954130248 + (0.008646 : ℝ) *
        (1 + 2 * (0.284434237826 + 0.011954130248) / (0.560485179969 * 110.932411855147))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12306]

end BstLean.Part264b.N12306

/-! The original eight local profiles supply actual 12306 moment certificates. -/
namespace BstLean.Part264b.N12306
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12306 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053410523855 ∧
    0 ≤ bN 12306 BstLean.Part154.csC (groupTheta g) ∧ bN 12306 BstLean.Part154.csC (groupTheta g) ≤ 0.001426654102 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12306 12306 0.011
      (momentAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12306 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12306 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12306 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231107169632 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12306 0.011
      (momentAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12306 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12306
/-! The actual computed-centre upper energy formula at 12306. -/
namespace BstLean.Part264b.N12306
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12306

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12306
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12306 cell12306)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086736188278
  | 2 => 0.087704176817
  | 3 => 0.088674351400
  | 4 => 0.089649032298
  | 5 => 0.090630990998
  | 6 => 0.091623512507
  | 7 => 0.092630462679
  | 8 => 0.093656360474
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12306 12306 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12306 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12306

/-! Actual upper energy certificates on all 43 source endpoints at 12306. -/
namespace BstLean.Part264b.N12306
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12306 cell12306)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12306 (gMinus 12306) (1 - (cell12306 i).lower) ≤ 1 ∧
    energyUpper 12306 (gMinus 12306) (BstLean.Part211.gPlus 12306)
      (finiteEnergy 12306 12306 0.011) (1 - (cell12306 i).lower) ≤
      (cell12306 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12306) (by norm_num)
        (q := 1 - (cell12306 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12306,cell12306]) (by norm_num [scalarRow12306,cell12306])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12306,cell12306])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12306

/-! Source-cell containment and simple scalar guards at 12306. -/
namespace BstLean.Part264b.N12306
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12306 cell12306)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12306 ⟨10,by decide⟩).lower ∧ (cell12306 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12306 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12306 ⟨11,by decide⟩).lower ∧ (cell12306 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12306 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12306 ⟨12,by decide⟩).lower ∧ (cell12306 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12306 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12306 ⟨13,by decide⟩).lower ∧ (cell12306 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12306 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12306 ⟨14,by decide⟩).lower ∧ (cell12306 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12306 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12306 ⟨15,by decide⟩).lower ∧ (cell12306 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12306 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12306 ⟨16,by decide⟩).lower ∧ (cell12306 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12306 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12306 ⟨17,by decide⟩).lower ∧ (cell12306 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12306 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12306 ⟨18,by decide⟩).lower ∧ (cell12306 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12306 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12306 ⟨19,by decide⟩).lower ∧ (cell12306 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12306 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12306 ⟨20,by decide⟩).lower ∧ (cell12306 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12306 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12306 ⟨21,by decide⟩).lower ∧ (cell12306 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12306 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12306 ⟨22,by decide⟩).lower ∧ (cell12306 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12306 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12306 ⟨23,by decide⟩).lower ∧ (cell12306 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12306 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12306 ⟨24,by decide⟩).lower ∧ (cell12306 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12306 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12306 ⟨25,by decide⟩).lower ∧ (cell12306 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12306 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12306 ⟨26,by decide⟩).lower ∧ (cell12306 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12306 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12306 ⟨27,by decide⟩).lower ∧ (cell12306 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12306 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12306 ⟨28,by decide⟩).lower ∧ (cell12306 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12306 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12306 ⟨29,by decide⟩).lower ∧ (cell12306 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12306 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12306 ⟨30,by decide⟩).lower ∧ (cell12306 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12306 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12306 ⟨31,by decide⟩).lower ∧ (cell12306 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12306 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12306 ⟨32,by decide⟩).lower ∧ (cell12306 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12306 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12306 ⟨33,by decide⟩).lower ∧ (cell12306 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12306 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12306 ⟨34,by decide⟩).lower ∧ (cell12306 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12306 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12306 ⟨35,by decide⟩).lower ∧ (cell12306 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12306 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12306 ⟨36,by decide⟩).lower ∧ (cell12306 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12306 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12306 ⟨37,by decide⟩).lower ∧ (cell12306 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12306 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12306 ⟨38,by decide⟩).lower ∧ (cell12306 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12306 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12306 ⟨39,by decide⟩).lower ∧ (cell12306 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12306 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12306 ⟨40,by decide⟩).lower ∧ (cell12306 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12306 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12306 ⟨41,by decide⟩).lower ∧ (cell12306 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12306 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12306 ⟨42,by decide⟩).lower ∧ (cell12306 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12306 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12306 ⟨43,by decide⟩).lower ∧ (cell12306 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12306 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12306 ⟨44,by decide⟩).lower ∧ (cell12306 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12306 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12306 ⟨45,by decide⟩).lower ∧ (cell12306 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12306 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12306 ⟨46,by decide⟩).lower ∧ (cell12306 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12306 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12306 ⟨47,by decide⟩).lower ∧ (cell12306 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12306 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12306 ⟨48,by decide⟩).lower ∧ (cell12306 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12306 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12306 ⟨49,by decide⟩).lower ∧ (cell12306 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12306 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12306 ⟨50,by decide⟩).lower ∧ (cell12306 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12306 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12306 ⟨51,by decide⟩).lower ∧ (cell12306 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12306 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12306 ⟨52,by decide⟩).lower ∧ (cell12306 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12306 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12306 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12306 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12306,cell12306,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12306 i).lower ∧
    (cell12306 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12306 i).upper ≤ (0.532 : ℝ) ∧
    (cell12306 i).centre ≤ (0.1 : ℝ) ∧ (cell12306 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12306 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12306 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12306

/-! The local source numeric instances at 12306 have no network premises. -/
namespace BstLean.Part264b.N12306
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12306 cell12306)

noncomputable def sourceNumerics12306 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12306 (cell12306 i)
      scalarRow12306.M scalarRow12306.H scalarRow12306.xi := by
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
    energy_allowance := scalarRow12306.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12306]
    centre_nonneg := (scalarRow12306.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12306]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12306
/-! Actual 12307 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12307
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12307 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12307 12307 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12307.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12307 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12307 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12307 := gPlus_lower 12307
end BstLean.Part264b.N12307

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12307
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036381545140 : ℝ) ≤ wn 12307 := by
  have hn : √(12307 : ℝ) ≤ 110.936919012564 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12307 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.936919012564 ≤ 2 / √12307 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260067810 : ℝ) ≤ rhoBar 12307 BstLean.Part154.csC ∧
    rhoBar 12307 BstLean.Part154.csC ≤ 0.000260099193 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036381545140 : ℝ) / (1.295212 * 12307) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12307) := by gcongr
      _ ≤ (0.000260099193 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12307 BstLean.Part154.csC) ≤ 0.001040464424 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12307 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12307 BstLean.Part154.csC) (piBar (rhoBar 12307 BstLean.Part154.csC)) ≤ 0.000198665820 ∧
    cc1 (rhoBar 12307 BstLean.Part154.csC) (piBar (rhoBar 12307 BstLean.Part154.csC)) ≤ 0.000126412318 ∧
    cc2 (rhoBar 12307 BstLean.Part154.csC) ≤ 0.000073383244 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12307 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12307 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12307 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12307 BstLean.Part154.csC * nuR (rhoBar 12307 BstLean.Part154.csC)) ≤ 0.000520215299 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260099193 : ℝ) * 0.001040464424 := by gcongr
      _ ≤ (0.000520215299 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12307 BstLean.Part154.csC) * nuR (rhoBar 12307 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040464424 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12307 BstLean.Part154.csC) * rhoBar 12307 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260099193 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260099193 / 2 + 0.399 * 0.001040464424 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198665820 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520215299 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126412318 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260099193 / 1.414213562 := by gcongr
      _ ≤ (0.000073383244 : ℝ) := by norm_num

end BstLean.Part264b.N12307

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12307
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12307 BstLean.Part154.csC) (piBar (rhoBar 12307 BstLean.Part154.csC)) ≤ 1.70444E-7 := by
  have hr0 : 0 ≤ rhoBar 12307 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12307 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12307 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12307 BstLean.Part154.csC) (piBar (rhoBar 12307 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12307 BstLean.Part154.csC) (piBar (rhoBar 12307 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12307 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198665820 : ℝ) ^ 2 + 0.000126412318 ^ 2 + 3 * 0.000073383244 ^ 2 +
        2 * 0.797885 * 0.000198665820 * 0.000126412318 + 2 * 0.000198665820 * 0.000073383244 +
        4 * 0.797885 * 0.000126412318 * 0.000073383244 := by gcongr
    _ ≤ (1.70444E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12307 BstLean.Part154.csC Θ ≤ 0.002717230683 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12307 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12307 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12307 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12307 BstLean.Part154.csC) (piBar (rhoBar 12307 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12307 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70444E-7 / (0.000260067810 : ℝ) := by gcongr
    _ ≤ 0.002717230683 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12307 BstLean.Part154.csC Θ ≤ 0.003016574461 + 0.000686515917 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12307 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12307 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12307 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260099193 +
        (6863 / 10000) * 0.000260099193 * 12307 * 0.001040464424) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003016574461 + 0.000686515917 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12307 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12307 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12307 0.011 Θ ∧ gammaRatio 12307 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12307 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12307) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12307 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12307 0.011 Θ) :=
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
    badAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12307 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12307 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12307 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12307 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12307 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12307 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12307 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12307 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12307 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12307 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12307 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004116574461 + 0.003403746600 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12307

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12307
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12307 BstLean.Part154.csC) (piBar (rhoBar 12307 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12307 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12307 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12307 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12307 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12307 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12307 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12307 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12307 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12307 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12307 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12307 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12307 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053324877755 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12307) ≤ 0.010765014855 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12307 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010765014855 + 2 * 0.737676 / 12307) := by gcongr
    _ ≤ (0.053324877755 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12307 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12307

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12307
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485228130 : ℝ) ≤ plow 12307 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12307) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410141426)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426546109) : eMP 12307 0.011 xi bn ≤ 0.001227380132 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12307 : ℝ) * (1 - 0.011))) ≤ 0.000606797274 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001426546109 / (12307 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606797274 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606797274 : ℝ) + 3.141593 * 0.053410141426 / (12307 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001227380132 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410141426)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426546109) : PiBarMP 12307 12 0.011 xi bn ≤ 0.163839989057 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12307 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037769645339 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.325078744590 : ℝ) ≤ √((12307 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.936919012563 : ℝ) ≤ √12307 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12307) ≤ 0.125588563184 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037769645339 + 0.053410141426 * 1.772454 / (2 * (110.325078744590 : ℝ))) * (1 + 0.001227380132) +
        8 / (12307 * 110.936919012563) + 0.125588563184 := by gcongr
    _ ≤ (0.163839989057 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410141426)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426546109) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284431220001) :
    parallelOracle 12307 0.011 xi bn cd ≤ 0.164865281706 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12307 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12307 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485228130 : ℝ) ≤ plow 12307 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.936919012563 : ℝ) ≤ √12307 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284431220001 : ℝ) / (2 * 0.560485228130 * 110.936919012563)) * 0.163839989057 +
        0.284431220001 ^ 2 / (2 * 0.560485228130 * 110.936919012563) := by gcongr
    _ ≤ (0.164865281706 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053410141426) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426546109)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284431220001) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12307 12307 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485228130 : ℝ) ≤ plow 12307 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.936919012563 : ℝ) ≤ √12307 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12307 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12307 Θ 1.22 ≤ 0.011953644574 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.936919012563 := by gcongr <;> linarith
      _ ≤ (0.011953644574 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12307 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12307 12307 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12307 12307 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12307 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12307 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12307 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12307 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164865281706 + 0.011953644574 + (0.008646 : ℝ) *
        (1 + 2 * (0.284431220001 + 0.011953644574) / (0.560485228130 * 110.936919012563))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12307]

end BstLean.Part264b.N12307

/-! The original eight local profiles supply actual 12307 moment certificates. -/
namespace BstLean.Part264b.N12307
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12307 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053410141426 ∧
    0 ≤ bN 12307 BstLean.Part154.csC (groupTheta g) ∧ bN 12307 BstLean.Part154.csC (groupTheta g) ≤ 0.001426546109 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12307 12307 0.011
      (momentAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12307 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12307 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12307 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231106342246 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12307 0.011
      (momentAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12307 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12307
/-! The actual computed-centre upper energy formula at 12307. -/
namespace BstLean.Part264b.N12307
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12307

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12307
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12307 cell12307)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086732743953
  | 2 => 0.087700656025
  | 3 => 0.088670740980
  | 4 => 0.089645316233
  | 5 => 0.090627149942
  | 6 => 0.091619523256
  | 7 => 0.092626297593
  | 8 => 0.093651986836
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12307 12307 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12307 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12307

/-! Actual upper energy certificates on all 43 source endpoints at 12307. -/
namespace BstLean.Part264b.N12307
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12307 cell12307)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12307 (gMinus 12307) (1 - (cell12307 i).lower) ≤ 1 ∧
    energyUpper 12307 (gMinus 12307) (BstLean.Part211.gPlus 12307)
      (finiteEnergy 12307 12307 0.011) (1 - (cell12307 i).lower) ≤
      (cell12307 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12307) (by norm_num)
        (q := 1 - (cell12307 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12307,cell12307]) (by norm_num [scalarRow12307,cell12307])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12307,cell12307])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12307

/-! Source-cell containment and simple scalar guards at 12307. -/
namespace BstLean.Part264b.N12307
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12307 cell12307)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12307 ⟨10,by decide⟩).lower ∧ (cell12307 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12307 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12307 ⟨11,by decide⟩).lower ∧ (cell12307 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12307 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12307 ⟨12,by decide⟩).lower ∧ (cell12307 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12307 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12307 ⟨13,by decide⟩).lower ∧ (cell12307 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12307 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12307 ⟨14,by decide⟩).lower ∧ (cell12307 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12307 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12307 ⟨15,by decide⟩).lower ∧ (cell12307 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12307 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12307 ⟨16,by decide⟩).lower ∧ (cell12307 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12307 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12307 ⟨17,by decide⟩).lower ∧ (cell12307 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12307 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12307 ⟨18,by decide⟩).lower ∧ (cell12307 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12307 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12307 ⟨19,by decide⟩).lower ∧ (cell12307 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12307 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12307 ⟨20,by decide⟩).lower ∧ (cell12307 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12307 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12307 ⟨21,by decide⟩).lower ∧ (cell12307 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12307 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12307 ⟨22,by decide⟩).lower ∧ (cell12307 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12307 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12307 ⟨23,by decide⟩).lower ∧ (cell12307 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12307 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12307 ⟨24,by decide⟩).lower ∧ (cell12307 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12307 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12307 ⟨25,by decide⟩).lower ∧ (cell12307 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12307 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12307 ⟨26,by decide⟩).lower ∧ (cell12307 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12307 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12307 ⟨27,by decide⟩).lower ∧ (cell12307 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12307 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12307 ⟨28,by decide⟩).lower ∧ (cell12307 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12307 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12307 ⟨29,by decide⟩).lower ∧ (cell12307 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12307 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12307 ⟨30,by decide⟩).lower ∧ (cell12307 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12307 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12307 ⟨31,by decide⟩).lower ∧ (cell12307 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12307 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12307 ⟨32,by decide⟩).lower ∧ (cell12307 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12307 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12307 ⟨33,by decide⟩).lower ∧ (cell12307 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12307 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12307 ⟨34,by decide⟩).lower ∧ (cell12307 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12307 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12307 ⟨35,by decide⟩).lower ∧ (cell12307 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12307 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12307 ⟨36,by decide⟩).lower ∧ (cell12307 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12307 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12307 ⟨37,by decide⟩).lower ∧ (cell12307 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12307 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12307 ⟨38,by decide⟩).lower ∧ (cell12307 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12307 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12307 ⟨39,by decide⟩).lower ∧ (cell12307 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12307 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12307 ⟨40,by decide⟩).lower ∧ (cell12307 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12307 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12307 ⟨41,by decide⟩).lower ∧ (cell12307 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12307 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12307 ⟨42,by decide⟩).lower ∧ (cell12307 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12307 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12307 ⟨43,by decide⟩).lower ∧ (cell12307 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12307 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12307 ⟨44,by decide⟩).lower ∧ (cell12307 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12307 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12307 ⟨45,by decide⟩).lower ∧ (cell12307 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12307 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12307 ⟨46,by decide⟩).lower ∧ (cell12307 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12307 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12307 ⟨47,by decide⟩).lower ∧ (cell12307 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12307 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12307 ⟨48,by decide⟩).lower ∧ (cell12307 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12307 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12307 ⟨49,by decide⟩).lower ∧ (cell12307 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12307 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12307 ⟨50,by decide⟩).lower ∧ (cell12307 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12307 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12307 ⟨51,by decide⟩).lower ∧ (cell12307 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12307 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12307 ⟨52,by decide⟩).lower ∧ (cell12307 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12307 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12307 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12307 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12307,cell12307,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12307 i).lower ∧
    (cell12307 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12307 i).upper ≤ (0.532 : ℝ) ∧
    (cell12307 i).centre ≤ (0.1 : ℝ) ∧ (cell12307 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12307 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12307 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12307

/-! The local source numeric instances at 12307 have no network premises. -/
namespace BstLean.Part264b.N12307
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12307 cell12307)

noncomputable def sourceNumerics12307 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12307 (cell12307 i)
      scalarRow12307.M scalarRow12307.H scalarRow12307.xi := by
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
    energy_allowance := scalarRow12307.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12307]
    centre_nonneg := (scalarRow12307.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12307]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12307
/-! Actual 12308 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12308
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12308 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12308 12308 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12308.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12308 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12308 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12308 := gPlus_lower 12308
end BstLean.Part264b.N12308

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12308
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036380053944 : ℝ) ≤ wn 12308 := by
  have hn : √(12308 : ℝ) ≤ 110.941425986870 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12308 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.941425986870 ≤ 2 / √12308 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260046306 : ℝ) ≤ rhoBar 12308 BstLean.Part154.csC ∧
    rhoBar 12308 BstLean.Part154.csC ≤ 0.000260078060 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036380053944 : ℝ) / (1.295212 * 12308) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12308) := by gcongr
      _ ≤ (0.000260078060 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12308 BstLean.Part154.csC) ≤ 0.001040379881 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12308 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12308 BstLean.Part154.csC) (piBar (rhoBar 12308 BstLean.Part154.csC)) ≤ 0.000198649677 ∧
    cc1 (rhoBar 12308 BstLean.Part154.csC) (piBar (rhoBar 12308 BstLean.Part154.csC)) ≤ 0.000126402047 ∧
    cc2 (rhoBar 12308 BstLean.Part154.csC) ≤ 0.000073377282 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12308 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12308 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12308 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12308 BstLean.Part154.csC * nuR (rhoBar 12308 BstLean.Part154.csC)) ≤ 0.000520173030 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260078060 : ℝ) * 0.001040379881 := by gcongr
      _ ≤ (0.000520173030 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12308 BstLean.Part154.csC) * nuR (rhoBar 12308 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040379881 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12308 BstLean.Part154.csC) * rhoBar 12308 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260078060 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260078060 / 2 + 0.399 * 0.001040379881 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198649677 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520173030 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126402047 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260078060 / 1.414213562 := by gcongr
      _ ≤ (0.000073377282 : ℝ) := by norm_num

end BstLean.Part264b.N12308

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12308
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12308 BstLean.Part154.csC) (piBar (rhoBar 12308 BstLean.Part154.csC)) ≤ 1.70416E-7 := by
  have hr0 : 0 ≤ rhoBar 12308 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12308 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12308 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12308 BstLean.Part154.csC) (piBar (rhoBar 12308 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12308 BstLean.Part154.csC) (piBar (rhoBar 12308 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12308 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198649677 : ℝ) ^ 2 + 0.000126402047 ^ 2 + 3 * 0.000073377282 ^ 2 +
        2 * 0.797885 * 0.000198649677 * 0.000126402047 + 2 * 0.000198649677 * 0.000073377282 +
        4 * 0.797885 * 0.000126402047 * 0.000073377282 := by gcongr
    _ ≤ (1.70416E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12308 BstLean.Part154.csC Θ ≤ 0.002717008964 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12308 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12308 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12308 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12308 BstLean.Part154.csC) (piBar (rhoBar 12308 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12308 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70416E-7 / (0.000260046306 : ℝ) := by gcongr
    _ ≤ 0.002717008964 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12308 BstLean.Part154.csC Θ ≤ 0.003016329344 + 0.000686460138 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12308 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12308 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12308 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260078060 +
        (6863 / 10000) * 0.000260078060 * 12308 * 0.001040379881) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003016329344 + 0.000686460138 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12308 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12308 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12308 0.011 Θ ∧ gammaRatio 12308 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12308 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12308) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12308 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12308 0.011 Θ) :=
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
    badAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12308 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12308 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12308 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12308 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12308 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12308 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12308 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12308 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12308 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12308 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12308 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004116329344 + 0.003403469102 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12308

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12308
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12308 BstLean.Part154.csC) (piBar (rhoBar 12308 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12308 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12308 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12308 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12308 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12308 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12308 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12308 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12308 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12308 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12308 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12308 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12308 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053322687583 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12308) ≤ 0.010764577528 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12308 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010764577528 + 2 * 0.737676 / 12308) := by gcongr
    _ ≤ (0.053322687583 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12308 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12308

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12308
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485276283 : ℝ) ≤ plow 12308 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12308) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053409750623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426429707) : eMP 12308 0.011 xi bn ≤ 0.001227280097 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12308 : ℝ) * (1 - 0.011))) ≤ 0.000606747867 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001426429707 / (12308 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606747867 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606747867 : ℝ) + 3.141593 * 0.053409750623 / (12308 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001227280097 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053409750623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426429707) : PiBarMP 12308 12 0.011 xi bn ≤ 0.163833319047 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12308 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037768104361 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.329560861992 : ℝ) ≤ √((12308 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.941425986869 : ℝ) ≤ √12308 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12308) ≤ 0.125583461172 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037768104361 + 0.053409750623 * 1.772454 / (2 * (110.329560861992 : ℝ))) * (1 + 0.001227280097) +
        8 / (12308 * 110.941425986869) + 0.125583461172 := by gcongr
    _ ≤ (0.163833319047 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053409750623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426429707) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284428184323) :
    parallelOracle 12308 0.011 xi bn cd ≤ 0.164858536816 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12308 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12308 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485276283 : ℝ) ≤ plow 12308 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.941425986869 : ℝ) ≤ √12308 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284428184323 : ℝ) / (2 * 0.560485276283 * 110.941425986869)) * 0.163833319047 +
        0.284428184323 ^ 2 / (2 * 0.560485276283 * 110.941425986869) := by gcongr
    _ ≤ (0.164858536816 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053409750623) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426429707)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284428184323) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12308 12308 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485276283 : ℝ) ≤ plow 12308 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.941425986869 : ℝ) ≤ √12308 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12308 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12308 Θ 1.22 ≤ 0.011953158960 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.941425986869 := by gcongr <;> linarith
      _ ≤ (0.011953158960 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12308 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12308 12308 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12308 12308 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12308 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12308 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12308 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12308 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164858536816 + 0.011953158960 + (0.008646 : ℝ) *
        (1 + 2 * (0.284428184323 + 0.011953158960) / (0.560485276283 * 110.941425986869))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12308]

end BstLean.Part264b.N12308

/-! The original eight local profiles supply actual 12308 moment certificates. -/
namespace BstLean.Part264b.N12308
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12308 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053409750623 ∧
    0 ≤ bN 12308 BstLean.Part154.csC (groupTheta g) ∧ bN 12308 BstLean.Part154.csC (groupTheta g) ≤ 0.001426429707 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12308 12308 0.011
      (momentAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12308 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12308 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12308 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231105496740 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12308 0.011
      (momentAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12308 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12308
/-! The actual computed-centre upper energy formula at 12308. -/
namespace BstLean.Part264b.N12308
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12308

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12308
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12308 cell12308)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086729301275
  | 2 => 0.087697136955
  | 3 => 0.088667132374
  | 4 => 0.089641602094
  | 5 => 0.090623310947
  | 6 => 0.091615536232
  | 7 => 0.092622134933
  | 8 => 0.093647615862
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12308 12308 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12308 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12308

/-! Actual upper energy certificates on all 43 source endpoints at 12308. -/
namespace BstLean.Part264b.N12308
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12308 cell12308)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12308 (gMinus 12308) (1 - (cell12308 i).lower) ≤ 1 ∧
    energyUpper 12308 (gMinus 12308) (BstLean.Part211.gPlus 12308)
      (finiteEnergy 12308 12308 0.011) (1 - (cell12308 i).lower) ≤
      (cell12308 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12308) (by norm_num)
        (q := 1 - (cell12308 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12308,cell12308]) (by norm_num [scalarRow12308,cell12308])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12308,cell12308])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12308

/-! Source-cell containment and simple scalar guards at 12308. -/
namespace BstLean.Part264b.N12308
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12308 cell12308)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12308 ⟨10,by decide⟩).lower ∧ (cell12308 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12308 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12308 ⟨11,by decide⟩).lower ∧ (cell12308 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12308 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12308 ⟨12,by decide⟩).lower ∧ (cell12308 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12308 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12308 ⟨13,by decide⟩).lower ∧ (cell12308 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12308 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12308 ⟨14,by decide⟩).lower ∧ (cell12308 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12308 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12308 ⟨15,by decide⟩).lower ∧ (cell12308 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12308 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12308 ⟨16,by decide⟩).lower ∧ (cell12308 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12308 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12308 ⟨17,by decide⟩).lower ∧ (cell12308 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12308 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12308 ⟨18,by decide⟩).lower ∧ (cell12308 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12308 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12308 ⟨19,by decide⟩).lower ∧ (cell12308 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12308 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12308 ⟨20,by decide⟩).lower ∧ (cell12308 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12308 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12308 ⟨21,by decide⟩).lower ∧ (cell12308 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12308 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12308 ⟨22,by decide⟩).lower ∧ (cell12308 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12308 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12308 ⟨23,by decide⟩).lower ∧ (cell12308 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12308 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12308 ⟨24,by decide⟩).lower ∧ (cell12308 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12308 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12308 ⟨25,by decide⟩).lower ∧ (cell12308 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12308 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12308 ⟨26,by decide⟩).lower ∧ (cell12308 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12308 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12308 ⟨27,by decide⟩).lower ∧ (cell12308 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12308 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12308 ⟨28,by decide⟩).lower ∧ (cell12308 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12308 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12308 ⟨29,by decide⟩).lower ∧ (cell12308 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12308 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12308 ⟨30,by decide⟩).lower ∧ (cell12308 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12308 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12308 ⟨31,by decide⟩).lower ∧ (cell12308 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12308 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12308 ⟨32,by decide⟩).lower ∧ (cell12308 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12308 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12308 ⟨33,by decide⟩).lower ∧ (cell12308 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12308 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12308 ⟨34,by decide⟩).lower ∧ (cell12308 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12308 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12308 ⟨35,by decide⟩).lower ∧ (cell12308 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12308 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12308 ⟨36,by decide⟩).lower ∧ (cell12308 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12308 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12308 ⟨37,by decide⟩).lower ∧ (cell12308 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12308 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12308 ⟨38,by decide⟩).lower ∧ (cell12308 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12308 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12308 ⟨39,by decide⟩).lower ∧ (cell12308 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12308 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12308 ⟨40,by decide⟩).lower ∧ (cell12308 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12308 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12308 ⟨41,by decide⟩).lower ∧ (cell12308 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12308 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12308 ⟨42,by decide⟩).lower ∧ (cell12308 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12308 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12308 ⟨43,by decide⟩).lower ∧ (cell12308 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12308 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12308 ⟨44,by decide⟩).lower ∧ (cell12308 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12308 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12308 ⟨45,by decide⟩).lower ∧ (cell12308 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12308 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12308 ⟨46,by decide⟩).lower ∧ (cell12308 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12308 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12308 ⟨47,by decide⟩).lower ∧ (cell12308 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12308 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12308 ⟨48,by decide⟩).lower ∧ (cell12308 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12308 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12308 ⟨49,by decide⟩).lower ∧ (cell12308 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12308 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12308 ⟨50,by decide⟩).lower ∧ (cell12308 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12308 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12308 ⟨51,by decide⟩).lower ∧ (cell12308 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12308 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12308 ⟨52,by decide⟩).lower ∧ (cell12308 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12308 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12308 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12308 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12308,cell12308,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12308 i).lower ∧
    (cell12308 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12308 i).upper ≤ (0.532 : ℝ) ∧
    (cell12308 i).centre ≤ (0.1 : ℝ) ∧ (cell12308 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12308 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12308 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12308

/-! The local source numeric instances at 12308 have no network premises. -/
namespace BstLean.Part264b.N12308
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12308 cell12308)

noncomputable def sourceNumerics12308 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12308 (cell12308 i)
      scalarRow12308.M scalarRow12308.H scalarRow12308.xi := by
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
    energy_allowance := scalarRow12308.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12308]
    centre_nonneg := (scalarRow12308.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12308]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12308
/-! Actual 12309 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12309
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12309 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12309 12309 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12309.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12309 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12309 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12309 := gPlus_lower 12309
end BstLean.Part264b.N12309

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12309
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036378562930 : ℝ) ≤ wn 12309 := by
  have hn : √(12309 : ℝ) ≤ 110.945932778088 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12309 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.945932778088 ≤ 2 / √12309 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260024806 : ℝ) ≤ rhoBar 12309 BstLean.Part154.csC ∧
    rhoBar 12309 BstLean.Part154.csC ≤ 0.000260056931 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036378562930 : ℝ) / (1.295212 * 12309) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12309) := by gcongr
      _ ≤ (0.000260056931 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12309 BstLean.Part154.csC) ≤ 0.001040295354 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12309 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12309 BstLean.Part154.csC) (piBar (rhoBar 12309 BstLean.Part154.csC)) ≤ 0.000198633538 ∧
    cc1 (rhoBar 12309 BstLean.Part154.csC) (piBar (rhoBar 12309 BstLean.Part154.csC)) ≤ 0.000126391778 ∧
    cc2 (rhoBar 12309 BstLean.Part154.csC) ≤ 0.000073371320 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12309 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12309 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12309 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12309 BstLean.Part154.csC * nuR (rhoBar 12309 BstLean.Part154.csC)) ≤ 0.000520130770 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260056931 : ℝ) * 0.001040295354 := by gcongr
      _ ≤ (0.000520130770 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12309 BstLean.Part154.csC) * nuR (rhoBar 12309 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040295354 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12309 BstLean.Part154.csC) * rhoBar 12309 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260056931 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260056931 / 2 + 0.399 * 0.001040295354 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198633538 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520130770 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126391778 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260056931 / 1.414213562 := by gcongr
      _ ≤ (0.000073371320 : ℝ) := by norm_num

end BstLean.Part264b.N12309

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12309
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12309 BstLean.Part154.csC) (piBar (rhoBar 12309 BstLean.Part154.csC)) ≤ 1.70388E-7 := by
  have hr0 : 0 ≤ rhoBar 12309 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12309 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12309 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12309 BstLean.Part154.csC) (piBar (rhoBar 12309 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12309 BstLean.Part154.csC) (piBar (rhoBar 12309 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12309 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198633538 : ℝ) ^ 2 + 0.000126391778 ^ 2 + 3 * 0.000073371320 ^ 2 +
        2 * 0.797885 * 0.000198633538 * 0.000126391778 + 2 * 0.000198633538 * 0.000073371320 +
        4 * 0.797885 * 0.000126391778 * 0.000073371320 := by gcongr
    _ ≤ (1.70388E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12309 BstLean.Part154.csC Θ ≤ 0.002716787166 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12309 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12309 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12309 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12309 BstLean.Part154.csC) (piBar (rhoBar 12309 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12309 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70388E-7 / (0.000260024806 : ℝ) := by gcongr
    _ ≤ 0.002716787166 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12309 BstLean.Part154.csC Θ ≤ 0.003016084279 + 0.000686404369 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12309 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12309 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12309 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260056931 +
        (6863 / 10000) * 0.000260056931 * 12309 * 0.001040295354) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003016084279 + 0.000686404369 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12309 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12309 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12309 0.011 Θ ∧ gammaRatio 12309 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12309 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12309) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12309 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12309 0.011 Θ) :=
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
    badAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12309 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12309 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12309 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12309 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12309 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12309 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12309 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12309 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12309 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12309 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12309 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004116084279 + 0.003403191535 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12309

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12309
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12309 BstLean.Part154.csC) (piBar (rhoBar 12309 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12309 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12309 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12309 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12309 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12309 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12309 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12309 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12309 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12309 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12309 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12309 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12309 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053320497683 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12309) ≤ 0.010764140255 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12309 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010764140255 + 2 * 0.737676 / 12309) := by gcongr
    _ ≤ (0.053320497683 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12309 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12309

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12309
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485324429 : ℝ) ≤ plow 12309 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12309) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053409359835)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426313263) : eMP 12309 0.011 xi bn ≤ 0.001227180052 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12309 : ℝ) * (1 - 0.011))) ≤ 0.000606698455 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001426313263 / (12309 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606698455 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606698455 : ℝ) + 3.141593 * 0.053409359835 / (12309 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001227180052 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053409359835)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426313263) : PiBarMP 12309 12 0.011 xi bn ≤ 0.163826649041 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12309 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037766562764 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.334042797316 : ℝ) ≤ √((12309 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.945932778087 : ℝ) ≤ √12309 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12309) ≤ 0.125578359782 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037766562764 + 0.053409359835 * 1.772454 / (2 * (110.334042797316 : ℝ))) * (1 + 0.001227180052) +
        8 / (12309 * 110.945932778087) + 0.125578359782 := by gcongr
    _ ≤ (0.163826649041 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053409359835)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426313263) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284425148946) :
    parallelOracle 12309 0.011 xi bn cd ≤ 0.164851791939 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12309 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12309 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485324429 : ℝ) ≤ plow 12309 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.945932778087 : ℝ) ≤ √12309 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284425148946 : ℝ) / (2 * 0.560485324429 * 110.945932778087)) * 0.163826649041 +
        0.284425148946 ^ 2 / (2 * 0.560485324429 * 110.945932778087) := by gcongr
    _ ≤ (0.164851791939 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053409359835) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426313263)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284425148946) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12309 12309 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485324429 : ℝ) ≤ plow 12309 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.945932778087 : ℝ) ≤ √12309 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12309 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12309 Θ 1.22 ≤ 0.011952673405 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.945932778087 := by gcongr <;> linarith
      _ ≤ (0.011952673405 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12309 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12309 12309 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12309 12309 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12309 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12309 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12309 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12309 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164851791939 + 0.011952673405 + (0.008646 : ℝ) *
        (1 + 2 * (0.284425148946 + 0.011952673405) / (0.560485324429 * 110.945932778087))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12309]

end BstLean.Part264b.N12309

/-! The original eight local profiles supply actual 12309 moment certificates. -/
namespace BstLean.Part264b.N12309
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12309 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053409359835 ∧
    0 ≤ bN 12309 BstLean.Part154.csC (groupTheta g) ∧ bN 12309 BstLean.Part154.csC (groupTheta g) ≤ 0.001426313263 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12309 12309 0.011
      (momentAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12309 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12309 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12309 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231104651263 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12309 0.011
      (momentAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12309 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12309
/-! The actual computed-centre upper energy formula at 12309. -/
namespace BstLean.Part264b.N12309
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12309

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12309
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12309 cell12309)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086725860242
  | 2 => 0.087693619604
  | 3 => 0.088663525579
  | 4 => 0.089637889878
  | 5 => 0.090619474012
  | 6 => 0.091611551433
  | 7 => 0.092617974696
  | 8 => 0.093643247549
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12309 12309 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12309 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12309

/-! Actual upper energy certificates on all 43 source endpoints at 12309. -/
namespace BstLean.Part264b.N12309
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12309 cell12309)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12309 (gMinus 12309) (1 - (cell12309 i).lower) ≤ 1 ∧
    energyUpper 12309 (gMinus 12309) (BstLean.Part211.gPlus 12309)
      (finiteEnergy 12309 12309 0.011) (1 - (cell12309 i).lower) ≤
      (cell12309 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12309) (by norm_num)
        (q := 1 - (cell12309 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12309,cell12309]) (by norm_num [scalarRow12309,cell12309])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12309,cell12309])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12309

/-! Source-cell containment and simple scalar guards at 12309. -/
namespace BstLean.Part264b.N12309
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12309 cell12309)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12309 ⟨10,by decide⟩).lower ∧ (cell12309 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12309 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12309 ⟨11,by decide⟩).lower ∧ (cell12309 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12309 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12309 ⟨12,by decide⟩).lower ∧ (cell12309 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12309 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12309 ⟨13,by decide⟩).lower ∧ (cell12309 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12309 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12309 ⟨14,by decide⟩).lower ∧ (cell12309 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12309 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12309 ⟨15,by decide⟩).lower ∧ (cell12309 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12309 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12309 ⟨16,by decide⟩).lower ∧ (cell12309 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12309 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12309 ⟨17,by decide⟩).lower ∧ (cell12309 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12309 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12309 ⟨18,by decide⟩).lower ∧ (cell12309 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12309 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12309 ⟨19,by decide⟩).lower ∧ (cell12309 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12309 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12309 ⟨20,by decide⟩).lower ∧ (cell12309 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12309 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12309 ⟨21,by decide⟩).lower ∧ (cell12309 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12309 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12309 ⟨22,by decide⟩).lower ∧ (cell12309 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12309 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12309 ⟨23,by decide⟩).lower ∧ (cell12309 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12309 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12309 ⟨24,by decide⟩).lower ∧ (cell12309 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12309 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12309 ⟨25,by decide⟩).lower ∧ (cell12309 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12309 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12309 ⟨26,by decide⟩).lower ∧ (cell12309 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12309 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12309 ⟨27,by decide⟩).lower ∧ (cell12309 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12309 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12309 ⟨28,by decide⟩).lower ∧ (cell12309 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12309 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12309 ⟨29,by decide⟩).lower ∧ (cell12309 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12309 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12309 ⟨30,by decide⟩).lower ∧ (cell12309 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12309 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12309 ⟨31,by decide⟩).lower ∧ (cell12309 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12309 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12309 ⟨32,by decide⟩).lower ∧ (cell12309 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12309 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12309 ⟨33,by decide⟩).lower ∧ (cell12309 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12309 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12309 ⟨34,by decide⟩).lower ∧ (cell12309 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12309 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12309 ⟨35,by decide⟩).lower ∧ (cell12309 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12309 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12309 ⟨36,by decide⟩).lower ∧ (cell12309 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12309 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12309 ⟨37,by decide⟩).lower ∧ (cell12309 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12309 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12309 ⟨38,by decide⟩).lower ∧ (cell12309 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12309 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12309 ⟨39,by decide⟩).lower ∧ (cell12309 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12309 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12309 ⟨40,by decide⟩).lower ∧ (cell12309 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12309 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12309 ⟨41,by decide⟩).lower ∧ (cell12309 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12309 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12309 ⟨42,by decide⟩).lower ∧ (cell12309 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12309 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12309 ⟨43,by decide⟩).lower ∧ (cell12309 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12309 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12309 ⟨44,by decide⟩).lower ∧ (cell12309 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12309 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12309 ⟨45,by decide⟩).lower ∧ (cell12309 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12309 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12309 ⟨46,by decide⟩).lower ∧ (cell12309 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12309 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12309 ⟨47,by decide⟩).lower ∧ (cell12309 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12309 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12309 ⟨48,by decide⟩).lower ∧ (cell12309 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12309 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12309 ⟨49,by decide⟩).lower ∧ (cell12309 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12309 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12309 ⟨50,by decide⟩).lower ∧ (cell12309 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12309 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12309 ⟨51,by decide⟩).lower ∧ (cell12309 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12309 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12309 ⟨52,by decide⟩).lower ∧ (cell12309 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12309 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12309 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12309 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12309,cell12309,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12309 i).lower ∧
    (cell12309 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12309 i).upper ≤ (0.532 : ℝ) ∧
    (cell12309 i).centre ≤ (0.1 : ℝ) ∧ (cell12309 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12309 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12309 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12309

/-! The local source numeric instances at 12309 have no network premises. -/
namespace BstLean.Part264b.N12309
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12309 cell12309)

noncomputable def sourceNumerics12309 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12309 (cell12309 i)
      scalarRow12309.M scalarRow12309.H scalarRow12309.xi := by
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
    energy_allowance := scalarRow12309.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12309]
    centre_nonneg := (scalarRow12309.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12309]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12309
/-! Actual 12310 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12310
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12310 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12310 12310 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12310.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12310 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12310 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12310 := gPlus_lower 12310
end BstLean.Part264b.N12310

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12310
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036377072099 : ℝ) ≤ wn 12310 := by
  have hn : √(12310 : ℝ) ≤ 110.950439386242 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12310 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.950439386242 ≤ 2 / √12310 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260003309 : ℝ) ≤ rhoBar 12310 BstLean.Part154.csC ∧
    rhoBar 12310 BstLean.Part154.csC ≤ 0.000260035805 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036377072099 : ℝ) / (1.295212 * 12310) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12310) := by gcongr
      _ ≤ (0.000260035805 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12310 BstLean.Part154.csC) ≤ 0.001040210839 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12310 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12310 BstLean.Part154.csC) (piBar (rhoBar 12310 BstLean.Part154.csC)) ≤ 0.000198617401 ∧
    cc1 (rhoBar 12310 BstLean.Part154.csC) (piBar (rhoBar 12310 BstLean.Part154.csC)) ≤ 0.000126381510 ∧
    cc2 (rhoBar 12310 BstLean.Part154.csC) ≤ 0.000073365360 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12310 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12310 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12310 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12310 BstLean.Part154.csC * nuR (rhoBar 12310 BstLean.Part154.csC)) ≤ 0.000520088515 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260035805 : ℝ) * 0.001040210839 := by gcongr
      _ ≤ (0.000520088515 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12310 BstLean.Part154.csC) * nuR (rhoBar 12310 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040210839 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12310 BstLean.Part154.csC) * rhoBar 12310 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260035805 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260035805 / 2 + 0.399 * 0.001040210839 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198617401 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520088515 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126381510 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260035805 / 1.414213562 := by gcongr
      _ ≤ (0.000073365360 : ℝ) := by norm_num

end BstLean.Part264b.N12310

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12310
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12310 BstLean.Part154.csC) (piBar (rhoBar 12310 BstLean.Part154.csC)) ≤ 1.70361E-7 := by
  have hr0 : 0 ≤ rhoBar 12310 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12310 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12310 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12310 BstLean.Part154.csC) (piBar (rhoBar 12310 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12310 BstLean.Part154.csC) (piBar (rhoBar 12310 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12310 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198617401 : ℝ) ^ 2 + 0.000126381510 ^ 2 + 3 * 0.000073365360 ^ 2 +
        2 * 0.797885 * 0.000198617401 * 0.000126381510 + 2 * 0.000198617401 * 0.000073365360 +
        4 * 0.797885 * 0.000126381510 * 0.000073365360 := by gcongr
    _ ≤ (1.70361E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12310 BstLean.Part154.csC Θ ≤ 0.002716581247 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12310 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12310 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12310 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12310 BstLean.Part154.csC) (piBar (rhoBar 12310 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12310 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70361E-7 / (0.000260003309 : ℝ) := by gcongr
    _ ≤ 0.002716581247 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12310 BstLean.Part154.csC Θ ≤ 0.003015839245 + 0.000686348609 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12310 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12310 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12310 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260035805 +
        (6863 / 10000) * 0.000260035805 * 12310 * 0.001040210839) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003015839245 + 0.000686348609 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12310 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12310 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12310 0.011 Θ ∧ gammaRatio 12310 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12310 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12310) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12310 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12310 0.011 Θ) :=
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
    badAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12310 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12310 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12310 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12310 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12310 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12310 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12310 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12310 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12310 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12310 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12310 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004115839245 + 0.003402929856 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12310

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12310
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12310 BstLean.Part154.csC) (piBar (rhoBar 12310 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12310 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12310 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12310 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12310 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12310 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12310 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12310 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12310 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12310 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12310 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12310 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12310 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053318308051 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12310) ≤ 0.010763703035 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12310 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010763703035 + 2 * 0.737676 / 12310) := by gcongr
    _ ≤ (0.053318308051 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12310 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12310

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12310
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485372567 : ℝ) ≤ plow 12310 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12310) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408977420)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426205155) : eMP 12310 0.011 xi bn ≤ 0.001227083564 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12310 : ℝ) * (1 - 0.011))) ≤ 0.000606650820 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001426205155 / (12310 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606650820 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606650820 : ℝ) + 3.141593 * 0.053408977420 / (12310 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001227083564 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408977420)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426205155) : PiBarMP 12310 12 0.011 xi bn ≤ 0.163820090303 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12310 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037765131471 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.338524550584 : ℝ) ≤ √((12310 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.950439386241 : ℝ) ≤ √12310 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12310) ≤ 0.125573259014 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037765131471 + 0.053408977420 * 1.772454 / (2 * (110.338524550584 : ℝ))) * (1 + 0.001227083564) +
        8 / (12310 * 110.950439386241) + 0.125573259014 := by gcongr
    _ ≤ (0.163820090303 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408977420)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426205155) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284422131949) :
    parallelOracle 12310 0.011 xi bn cd ≤ 0.164845158702 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12310 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12310 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485372567 : ℝ) ≤ plow 12310 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.950439386241 : ℝ) ≤ √12310 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284422131949 : ℝ) / (2 * 0.560485372567 * 110.950439386241)) * 0.163820090303 +
        0.284422131949 ^ 2 / (2 * 0.560485372567 * 110.950439386241) := by gcongr
    _ ≤ (0.164845158702 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408977420) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426205155)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284422131949) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12310 12310 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485372567 : ℝ) ≤ plow 12310 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.950439386241 : ℝ) ≤ √12310 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12310 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12310 Θ 1.22 ≤ 0.011952187908 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.950439386241 := by gcongr <;> linarith
      _ ≤ (0.011952187908 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12310 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12310 12310 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12310 12310 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12310 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12310 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12310 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12310 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164845158702 + 0.011952187908 + (0.008646 : ℝ) *
        (1 + 2 * (0.284422131949 + 0.011952187908) / (0.560485372567 * 110.950439386241))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12310]

end BstLean.Part264b.N12310

/-! The original eight local profiles supply actual 12310 moment certificates. -/
namespace BstLean.Part264b.N12310
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12310 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053408977420 ∧
    0 ≤ bN 12310 BstLean.Part154.csC (groupTheta g) ∧ bN 12310 BstLean.Part154.csC (groupTheta g) ≤ 0.001426205155 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12310 12310 0.011
      (momentAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12310 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12310 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12310 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231103823898 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12310 0.011
      (momentAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12310 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12310
/-! The actual computed-centre upper energy formula at 12310. -/
namespace BstLean.Part264b.N12310
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12310

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12310
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12310 cell12310)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086722420852
  | 2 => 0.087690103971
  | 3 => 0.088659920592
  | 4 => 0.089634179582
  | 5 => 0.090615639134
  | 6 => 0.091607568855
  | 7 => 0.092613816879
  | 8 => 0.093638881893
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12310 12310 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12310 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12310

/-! Actual upper energy certificates on all 43 source endpoints at 12310. -/
namespace BstLean.Part264b.N12310
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12310 cell12310)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12310 (gMinus 12310) (1 - (cell12310 i).lower) ≤ 1 ∧
    energyUpper 12310 (gMinus 12310) (BstLean.Part211.gPlus 12310)
      (finiteEnergy 12310 12310 0.011) (1 - (cell12310 i).lower) ≤
      (cell12310 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12310) (by norm_num)
        (q := 1 - (cell12310 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12310,cell12310]) (by norm_num [scalarRow12310,cell12310])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12310,cell12310])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12310

/-! Source-cell containment and simple scalar guards at 12310. -/
namespace BstLean.Part264b.N12310
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12310 cell12310)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12310 ⟨10,by decide⟩).lower ∧ (cell12310 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12310 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12310 ⟨11,by decide⟩).lower ∧ (cell12310 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12310 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12310 ⟨12,by decide⟩).lower ∧ (cell12310 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12310 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12310 ⟨13,by decide⟩).lower ∧ (cell12310 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12310 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12310 ⟨14,by decide⟩).lower ∧ (cell12310 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12310 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12310 ⟨15,by decide⟩).lower ∧ (cell12310 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12310 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12310 ⟨16,by decide⟩).lower ∧ (cell12310 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12310 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12310 ⟨17,by decide⟩).lower ∧ (cell12310 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12310 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12310 ⟨18,by decide⟩).lower ∧ (cell12310 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12310 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12310 ⟨19,by decide⟩).lower ∧ (cell12310 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12310 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12310 ⟨20,by decide⟩).lower ∧ (cell12310 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12310 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12310 ⟨21,by decide⟩).lower ∧ (cell12310 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12310 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12310 ⟨22,by decide⟩).lower ∧ (cell12310 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12310 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12310 ⟨23,by decide⟩).lower ∧ (cell12310 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12310 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12310 ⟨24,by decide⟩).lower ∧ (cell12310 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12310 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12310 ⟨25,by decide⟩).lower ∧ (cell12310 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12310 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12310 ⟨26,by decide⟩).lower ∧ (cell12310 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12310 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12310 ⟨27,by decide⟩).lower ∧ (cell12310 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12310 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12310 ⟨28,by decide⟩).lower ∧ (cell12310 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12310 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12310 ⟨29,by decide⟩).lower ∧ (cell12310 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12310 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12310 ⟨30,by decide⟩).lower ∧ (cell12310 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12310 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12310 ⟨31,by decide⟩).lower ∧ (cell12310 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12310 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12310 ⟨32,by decide⟩).lower ∧ (cell12310 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12310 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12310 ⟨33,by decide⟩).lower ∧ (cell12310 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12310 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12310 ⟨34,by decide⟩).lower ∧ (cell12310 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12310 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12310 ⟨35,by decide⟩).lower ∧ (cell12310 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12310 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12310 ⟨36,by decide⟩).lower ∧ (cell12310 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12310 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12310 ⟨37,by decide⟩).lower ∧ (cell12310 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12310 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12310 ⟨38,by decide⟩).lower ∧ (cell12310 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12310 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12310 ⟨39,by decide⟩).lower ∧ (cell12310 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12310 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12310 ⟨40,by decide⟩).lower ∧ (cell12310 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12310 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12310 ⟨41,by decide⟩).lower ∧ (cell12310 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12310 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12310 ⟨42,by decide⟩).lower ∧ (cell12310 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12310 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12310 ⟨43,by decide⟩).lower ∧ (cell12310 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12310 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12310 ⟨44,by decide⟩).lower ∧ (cell12310 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12310 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12310 ⟨45,by decide⟩).lower ∧ (cell12310 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12310 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12310 ⟨46,by decide⟩).lower ∧ (cell12310 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12310 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12310 ⟨47,by decide⟩).lower ∧ (cell12310 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12310 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12310 ⟨48,by decide⟩).lower ∧ (cell12310 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12310 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12310 ⟨49,by decide⟩).lower ∧ (cell12310 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12310 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12310 ⟨50,by decide⟩).lower ∧ (cell12310 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12310 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12310 ⟨51,by decide⟩).lower ∧ (cell12310 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12310 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12310 ⟨52,by decide⟩).lower ∧ (cell12310 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12310 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12310 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12310 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12310,cell12310,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12310 i).lower ∧
    (cell12310 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12310 i).upper ≤ (0.532 : ℝ) ∧
    (cell12310 i).centre ≤ (0.1 : ℝ) ∧ (cell12310 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12310 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12310 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12310

/-! The local source numeric instances at 12310 have no network premises. -/
namespace BstLean.Part264b.N12310
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12310 cell12310)

noncomputable def sourceNumerics12310 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12310 (cell12310 i)
      scalarRow12310.M scalarRow12310.H scalarRow12310.xi := by
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
    energy_allowance := scalarRow12310.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12310]
    centre_nonneg := (scalarRow12310.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12310]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12310
/-! Actual 12311 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12311
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12311 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12311 12311 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12311.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12311 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12311 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12311 := gPlus_lower 12311
end BstLean.Part264b.N12311

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12311
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036375581451 : ℝ) ≤ wn 12311 := by
  have hn : √(12311 : ℝ) ≤ 110.954945811352 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12311 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.954945811352 ≤ 2 / √12311 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259981815 : ℝ) ≤ rhoBar 12311 BstLean.Part154.csC ∧
    rhoBar 12311 BstLean.Part154.csC ≤ 0.000260014683 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036375581451 : ℝ) / (1.295212 * 12311) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12311) := by gcongr
      _ ≤ (0.000260014683 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12311 BstLean.Part154.csC) ≤ 0.001040126340 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12311 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12311 BstLean.Part154.csC) (piBar (rhoBar 12311 BstLean.Part154.csC)) ≤ 0.000198601267 ∧
    cc1 (rhoBar 12311 BstLean.Part154.csC) (piBar (rhoBar 12311 BstLean.Part154.csC)) ≤ 0.000126371244 ∧
    cc2 (rhoBar 12311 BstLean.Part154.csC) ≤ 0.000073359401 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12311 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12311 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12311 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12311 BstLean.Part154.csC * nuR (rhoBar 12311 BstLean.Part154.csC)) ≤ 0.000520046268 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260014683 : ℝ) * 0.001040126340 := by gcongr
      _ ≤ (0.000520046268 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12311 BstLean.Part154.csC) * nuR (rhoBar 12311 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040126340 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12311 BstLean.Part154.csC) * rhoBar 12311 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260014683 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260014683 / 2 + 0.399 * 0.001040126340 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198601267 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520046268 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126371244 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260014683 / 1.414213562 := by gcongr
      _ ≤ (0.000073359401 : ℝ) := by norm_num

end BstLean.Part264b.N12311

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12311
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12311 BstLean.Part154.csC) (piBar (rhoBar 12311 BstLean.Part154.csC)) ≤ 1.70333E-7 := by
  have hr0 : 0 ≤ rhoBar 12311 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12311 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12311 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12311 BstLean.Part154.csC) (piBar (rhoBar 12311 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12311 BstLean.Part154.csC) (piBar (rhoBar 12311 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12311 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198601267 : ℝ) ^ 2 + 0.000126371244 ^ 2 + 3 * 0.000073359401 ^ 2 +
        2 * 0.797885 * 0.000198601267 * 0.000126371244 + 2 * 0.000198601267 * 0.000073359401 +
        4 * 0.797885 * 0.000126371244 * 0.000073359401 := by gcongr
    _ ≤ (1.70333E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12311 BstLean.Part154.csC Θ ≤ 0.002716359315 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12311 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12311 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12311 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12311 BstLean.Part154.csC) (piBar (rhoBar 12311 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12311 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70333E-7 / (0.000259981815 : ℝ) := by gcongr
    _ ≤ 0.002716359315 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12311 BstLean.Part154.csC Θ ≤ 0.003015594263 + 0.000686292858 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12311 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12311 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12311 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260014683 +
        (6863 / 10000) * 0.000260014683 * 12311 * 0.001040126340) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003015594263 + 0.000686292858 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12311 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12311 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12311 0.011 Θ ∧ gammaRatio 12311 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12311 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12311) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12311 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12311 0.011 Θ) :=
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
    badAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12311 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12311 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12311 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12311 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12311 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12311 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12311 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12311 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12311 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12311 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12311 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004115594263 + 0.003402652173 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12311

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12311
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12311 BstLean.Part154.csC) (piBar (rhoBar 12311 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12311 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12311 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12311 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12311 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12311 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12311 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12311 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12311 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12311 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12311 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12311 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12311 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053316118686 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12311) ≤ 0.010763265868 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12311 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010763265868 + 2 * 0.737676 / 12311) := by gcongr
    _ ≤ (0.053316118686 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12311 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12311

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12311
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485420696 : ℝ) ≤ plow 12311 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12311) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408586654)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426088641) : eMP 12311 0.011 xi bn ≤ 0.001226983508 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12311 : ℝ) * (1 - 0.011))) ≤ 0.000606601402 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001426088641 / (12311 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606601402 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606601402 : ℝ) + 3.141593 * 0.053408586654 / (12311 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001226983508 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408586654)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426088641) : PiBarMP 12311 12 0.011 xi bn ≤ 0.163813420498 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12311 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037763588826 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.343006121819 : ℝ) ≤ √((12311 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.954945811351 : ℝ) ≤ √12311 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12311) ≤ 0.125568158868 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037763588826 + 0.053408586654 * 1.772454 / (2 * (110.343006121819 : ℝ))) * (1 + 0.001226983508) +
        8 / (12311 * 110.954945811351) + 0.125568158868 := by gcongr
    _ ≤ (0.163813420498 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408586654)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426088641) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284419097148) :
    parallelOracle 12311 0.011 xi bn cd ≤ 0.164838414047 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12311 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12311 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485420696 : ℝ) ≤ plow 12311 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.954945811351 : ℝ) ≤ √12311 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284419097148 : ℝ) / (2 * 0.560485420696 * 110.954945811351)) * 0.163813420498 +
        0.284419097148 ^ 2 / (2 * 0.560485420696 * 110.954945811351) := by gcongr
    _ ≤ (0.164838414047 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408586654) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001426088641)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284419097148) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12311 12311 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485420696 : ℝ) ≤ plow 12311 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.954945811351 : ℝ) ≤ √12311 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12311 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12311 Θ 1.22 ≤ 0.011951702471 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.954945811351 := by gcongr <;> linarith
      _ ≤ (0.011951702471 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12311 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12311 12311 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12311 12311 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12311 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12311 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12311 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12311 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164838414047 + 0.011951702471 + (0.008646 : ℝ) *
        (1 + 2 * (0.284419097148 + 0.011951702471) / (0.560485420696 * 110.954945811351))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12311]

end BstLean.Part264b.N12311

/-! The original eight local profiles supply actual 12311 moment certificates. -/
namespace BstLean.Part264b.N12311
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12311 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053408586654 ∧
    0 ≤ bN 12311 BstLean.Part154.csC (groupTheta g) ∧ bN 12311 BstLean.Part154.csC (groupTheta g) ≤ 0.001426088641 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12311 12311 0.011
      (momentAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12311 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12311 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12311 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231102978462 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12311 0.011
      (momentAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12311 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12311
/-! The actual computed-centre upper energy formula at 12311. -/
namespace BstLean.Part264b.N12311
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12311

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12311
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12311 cell12311)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086718983104
  | 2 => 0.087686590053
  | 3 => 0.088656317412
  | 4 => 0.089630471206
  | 5 => 0.090611806311
  | 6 => 0.091603588498
  | 7 => 0.092609661480
  | 8 => 0.093634518891
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12311 12311 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12311 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12311

/-! Actual upper energy certificates on all 43 source endpoints at 12311. -/
namespace BstLean.Part264b.N12311
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12311 cell12311)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12311 (gMinus 12311) (1 - (cell12311 i).lower) ≤ 1 ∧
    energyUpper 12311 (gMinus 12311) (BstLean.Part211.gPlus 12311)
      (finiteEnergy 12311 12311 0.011) (1 - (cell12311 i).lower) ≤
      (cell12311 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12311) (by norm_num)
        (q := 1 - (cell12311 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12311,cell12311]) (by norm_num [scalarRow12311,cell12311])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12311,cell12311])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12311

/-! Source-cell containment and simple scalar guards at 12311. -/
namespace BstLean.Part264b.N12311
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12311 cell12311)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12311 ⟨10,by decide⟩).lower ∧ (cell12311 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12311 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12311 ⟨11,by decide⟩).lower ∧ (cell12311 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12311 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12311 ⟨12,by decide⟩).lower ∧ (cell12311 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12311 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12311 ⟨13,by decide⟩).lower ∧ (cell12311 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12311 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12311 ⟨14,by decide⟩).lower ∧ (cell12311 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12311 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12311 ⟨15,by decide⟩).lower ∧ (cell12311 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12311 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12311 ⟨16,by decide⟩).lower ∧ (cell12311 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12311 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12311 ⟨17,by decide⟩).lower ∧ (cell12311 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12311 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12311 ⟨18,by decide⟩).lower ∧ (cell12311 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12311 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12311 ⟨19,by decide⟩).lower ∧ (cell12311 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12311 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12311 ⟨20,by decide⟩).lower ∧ (cell12311 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12311 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12311 ⟨21,by decide⟩).lower ∧ (cell12311 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12311 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12311 ⟨22,by decide⟩).lower ∧ (cell12311 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12311 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12311 ⟨23,by decide⟩).lower ∧ (cell12311 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12311 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12311 ⟨24,by decide⟩).lower ∧ (cell12311 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12311 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12311 ⟨25,by decide⟩).lower ∧ (cell12311 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12311 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12311 ⟨26,by decide⟩).lower ∧ (cell12311 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12311 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12311 ⟨27,by decide⟩).lower ∧ (cell12311 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12311 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12311 ⟨28,by decide⟩).lower ∧ (cell12311 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12311 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12311 ⟨29,by decide⟩).lower ∧ (cell12311 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12311 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12311 ⟨30,by decide⟩).lower ∧ (cell12311 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12311 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12311 ⟨31,by decide⟩).lower ∧ (cell12311 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12311 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12311 ⟨32,by decide⟩).lower ∧ (cell12311 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12311 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12311 ⟨33,by decide⟩).lower ∧ (cell12311 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12311 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12311 ⟨34,by decide⟩).lower ∧ (cell12311 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12311 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12311 ⟨35,by decide⟩).lower ∧ (cell12311 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12311 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12311 ⟨36,by decide⟩).lower ∧ (cell12311 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12311 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12311 ⟨37,by decide⟩).lower ∧ (cell12311 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12311 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12311 ⟨38,by decide⟩).lower ∧ (cell12311 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12311 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12311 ⟨39,by decide⟩).lower ∧ (cell12311 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12311 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12311 ⟨40,by decide⟩).lower ∧ (cell12311 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12311 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12311 ⟨41,by decide⟩).lower ∧ (cell12311 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12311 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12311 ⟨42,by decide⟩).lower ∧ (cell12311 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12311 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12311 ⟨43,by decide⟩).lower ∧ (cell12311 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12311 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12311 ⟨44,by decide⟩).lower ∧ (cell12311 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12311 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12311 ⟨45,by decide⟩).lower ∧ (cell12311 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12311 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12311 ⟨46,by decide⟩).lower ∧ (cell12311 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12311 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12311 ⟨47,by decide⟩).lower ∧ (cell12311 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12311 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12311 ⟨48,by decide⟩).lower ∧ (cell12311 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12311 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12311 ⟨49,by decide⟩).lower ∧ (cell12311 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12311 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12311 ⟨50,by decide⟩).lower ∧ (cell12311 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12311 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12311 ⟨51,by decide⟩).lower ∧ (cell12311 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12311 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12311 ⟨52,by decide⟩).lower ∧ (cell12311 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12311 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12311 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12311 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12311,cell12311,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12311 i).lower ∧
    (cell12311 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12311 i).upper ≤ (0.532 : ℝ) ∧
    (cell12311 i).centre ≤ (0.1 : ℝ) ∧ (cell12311 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12311 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12311 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12311

/-! The local source numeric instances at 12311 have no network premises. -/
namespace BstLean.Part264b.N12311
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12311 cell12311)

noncomputable def sourceNumerics12311 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12311 (cell12311 i)
      scalarRow12311.M scalarRow12311.H scalarRow12311.xi := by
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
    energy_allowance := scalarRow12311.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12311]
    centre_nonneg := (scalarRow12311.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12311]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12311
/-! Actual 12312 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12312
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12312 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12312 12312 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12312.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12312 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12312 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12312 := gPlus_lower 12312
end BstLean.Part264b.N12312

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12312
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036374090985 : ℝ) ≤ wn 12312 := by
  have hn : √(12312 : ℝ) ≤ 110.959452053442 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12312 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.959452053442 ≤ 2 / √12312 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259960325 : ℝ) ≤ rhoBar 12312 BstLean.Part154.csC ∧
    rhoBar 12312 BstLean.Part154.csC ≤ 0.000259993564 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036374090985 : ℝ) / (1.295212 * 12312) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12312) := by gcongr
      _ ≤ (0.000259993564 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12312 BstLean.Part154.csC) ≤ 0.001040041853 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12312 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12312 BstLean.Part154.csC) (piBar (rhoBar 12312 BstLean.Part154.csC)) ≤ 0.000198585136 ∧
    cc1 (rhoBar 12312 BstLean.Part154.csC) (piBar (rhoBar 12312 BstLean.Part154.csC)) ≤ 0.000126360979 ∧
    cc2 (rhoBar 12312 BstLean.Part154.csC) ≤ 0.000073353442 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12312 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12312 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12312 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12312 BstLean.Part154.csC * nuR (rhoBar 12312 BstLean.Part154.csC)) ≤ 0.000520004027 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259993564 : ℝ) * 0.001040041853 := by gcongr
      _ ≤ (0.000520004027 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12312 BstLean.Part154.csC) * nuR (rhoBar 12312 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001040041853 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12312 BstLean.Part154.csC) * rhoBar 12312 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259993564 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259993564 / 2 + 0.399 * 0.001040041853 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198585136 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520004027 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126360979 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259993564 / 1.414213562 := by gcongr
      _ ≤ (0.000073353442 : ℝ) := by norm_num

end BstLean.Part264b.N12312

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12312
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12312 BstLean.Part154.csC) (piBar (rhoBar 12312 BstLean.Part154.csC)) ≤ 1.70305E-7 := by
  have hr0 : 0 ≤ rhoBar 12312 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12312 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12312 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12312 BstLean.Part154.csC) (piBar (rhoBar 12312 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12312 BstLean.Part154.csC) (piBar (rhoBar 12312 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12312 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198585136 : ℝ) ^ 2 + 0.000126360979 ^ 2 + 3 * 0.000073353442 ^ 2 +
        2 * 0.797885 * 0.000198585136 * 0.000126360979 + 2 * 0.000198585136 * 0.000073353442 +
        4 * 0.797885 * 0.000126360979 * 0.000073353442 := by gcongr
    _ ≤ (1.70305E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12312 BstLean.Part154.csC Θ ≤ 0.002716137304 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12312 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12312 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12312 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12312 BstLean.Part154.csC) (piBar (rhoBar 12312 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12312 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70305E-7 / (0.000259960325 : ℝ) := by gcongr
    _ ≤ 0.002716137304 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12312 BstLean.Part154.csC Θ ≤ 0.003015349311 + 0.000686237116 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12312 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12312 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12312 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259993564 +
        (6863 / 10000) * 0.000259993564 * 12312 * 0.001040041853) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003015349311 + 0.000686237116 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12312 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12312 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12312 0.011 Θ ∧ gammaRatio 12312 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12312 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12312) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12312 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12312 0.011 Θ) :=
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
    badAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12312 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12312 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12312 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12312 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12312 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12312 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12312 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12312 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12312 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12312 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12312 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004115349311 + 0.003402374420 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12312

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12312
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12312 BstLean.Part154.csC) (piBar (rhoBar 12312 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12312 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12312 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12312 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12312 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12312 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12312 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12312 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12312 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12312 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12312 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12312 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12312 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053313929589 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12312) ≤ 0.010762828754 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12312 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010762828754 + 2 * 0.737676 / 12312) := by gcongr
    _ ≤ (0.053313929589 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12312 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12312

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12312
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485468819 : ℝ) ≤ plow 12312 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12312) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408195882)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425972085) : eMP 12312 0.011 xi bn ≤ 0.001226883440 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12312 : ℝ) * (1 - 0.011))) ≤ 0.000606551978 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001425972085 / (12312 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606551978 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606551978 : ℝ) + 3.141593 * 0.053408195882 / (12312 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001226883440 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408195882)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425972085) : PiBarMP 12312 12 0.011 xi bn ≤ 0.163806750696 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12312 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037762045562 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.347487511043 : ℝ) ≤ √((12312 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.959452053441 : ℝ) ≤ √12312 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12312) ≤ 0.125563059343 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037762045562 + 0.053408195882 * 1.772454 / (2 * (110.347487511043 : ℝ))) * (1 + 0.001226883440) +
        8 / (12312 * 110.959452053441) + 0.125563059343 := by gcongr
    _ ≤ (0.163806750696 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408195882)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425972085) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284416062600) :
    parallelOracle 12312 0.011 xi bn cd ≤ 0.164831669404 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12312 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12312 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485468819 : ℝ) ≤ plow 12312 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.959452053441 : ℝ) ≤ √12312 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284416062600 : ℝ) / (2 * 0.560485468819 * 110.959452053441)) * 0.163806750696 +
        0.284416062600 ^ 2 / (2 * 0.560485468819 * 110.959452053441) := by gcongr
    _ ≤ (0.164831669404 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053408195882) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425972085)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284416062600) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12312 12312 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485468819 : ℝ) ≤ plow 12312 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.959452053441 : ℝ) ≤ √12312 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12312 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12312 Θ 1.22 ≤ 0.011951217093 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.959452053441 := by gcongr <;> linarith
      _ ≤ (0.011951217093 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12312 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12312 12312 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12312 12312 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12312 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12312 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12312 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12312 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164831669404 + 0.011951217093 + (0.008646 : ℝ) *
        (1 + 2 * (0.284416062600 + 0.011951217093) / (0.560485468819 * 110.959452053441))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12312]

end BstLean.Part264b.N12312

/-! The original eight local profiles supply actual 12312 moment certificates. -/
namespace BstLean.Part264b.N12312
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12312 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053408195882 ∧
    0 ≤ bN 12312 BstLean.Part154.csC (groupTheta g) ∧ bN 12312 BstLean.Part154.csC (groupTheta g) ≤ 0.001425972085 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12312 12312 0.011
      (momentAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12312 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12312 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12312 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231102133011 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12312 0.011
      (momentAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12312 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12312
/-! The actual computed-centre upper energy formula at 12312. -/
namespace BstLean.Part264b.N12312
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12312

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12312
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12312 cell12312)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086715546994
  | 2 => 0.087683077849
  | 3 => 0.088652716037
  | 4 => 0.089626764745
  | 5 => 0.090607975540
  | 6 => 0.091599610357
  | 7 => 0.092605508495
  | 8 => 0.093630158541
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12312 12312 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12312 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.004138 + 0.0034293 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part264b.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part264b.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12312

/-! Actual upper energy certificates on all 43 source endpoints at 12312. -/
namespace BstLean.Part264b.N12312
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12312 cell12312)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12312 (gMinus 12312) (1 - (cell12312 i).lower) ≤ 1 ∧
    energyUpper 12312 (gMinus 12312) (BstLean.Part211.gPlus 12312)
      (finiteEnergy 12312 12312 0.011) (1 - (cell12312 i).lower) ≤
      (cell12312 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12312) (by norm_num)
        (q := 1 - (cell12312 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12312,cell12312]) (by norm_num [scalarRow12312,cell12312])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12312,cell12312])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12312

/-! Source-cell containment and simple scalar guards at 12312. -/
namespace BstLean.Part264b.N12312
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12312 cell12312)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12312 ⟨10,by decide⟩).lower ∧ (cell12312 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12312 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12312 ⟨11,by decide⟩).lower ∧ (cell12312 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12312 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12312 ⟨12,by decide⟩).lower ∧ (cell12312 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12312 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12312 ⟨13,by decide⟩).lower ∧ (cell12312 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12312 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12312 ⟨14,by decide⟩).lower ∧ (cell12312 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12312 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12312 ⟨15,by decide⟩).lower ∧ (cell12312 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12312 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12312 ⟨16,by decide⟩).lower ∧ (cell12312 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12312 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12312 ⟨17,by decide⟩).lower ∧ (cell12312 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12312 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12312 ⟨18,by decide⟩).lower ∧ (cell12312 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12312 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12312 ⟨19,by decide⟩).lower ∧ (cell12312 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12312 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12312 ⟨20,by decide⟩).lower ∧ (cell12312 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12312 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12312 ⟨21,by decide⟩).lower ∧ (cell12312 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12312 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12312 ⟨22,by decide⟩).lower ∧ (cell12312 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12312 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12312 ⟨23,by decide⟩).lower ∧ (cell12312 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12312 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12312 ⟨24,by decide⟩).lower ∧ (cell12312 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12312 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12312 ⟨25,by decide⟩).lower ∧ (cell12312 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12312 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12312 ⟨26,by decide⟩).lower ∧ (cell12312 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12312 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12312 ⟨27,by decide⟩).lower ∧ (cell12312 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12312 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12312 ⟨28,by decide⟩).lower ∧ (cell12312 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12312 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12312 ⟨29,by decide⟩).lower ∧ (cell12312 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12312 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12312 ⟨30,by decide⟩).lower ∧ (cell12312 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12312 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12312 ⟨31,by decide⟩).lower ∧ (cell12312 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12312 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12312 ⟨32,by decide⟩).lower ∧ (cell12312 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12312 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12312 ⟨33,by decide⟩).lower ∧ (cell12312 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12312 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12312 ⟨34,by decide⟩).lower ∧ (cell12312 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12312 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12312 ⟨35,by decide⟩).lower ∧ (cell12312 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12312 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12312 ⟨36,by decide⟩).lower ∧ (cell12312 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12312 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12312 ⟨37,by decide⟩).lower ∧ (cell12312 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12312 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12312 ⟨38,by decide⟩).lower ∧ (cell12312 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12312 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12312 ⟨39,by decide⟩).lower ∧ (cell12312 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12312 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12312 ⟨40,by decide⟩).lower ∧ (cell12312 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12312 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12312 ⟨41,by decide⟩).lower ∧ (cell12312 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12312 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12312 ⟨42,by decide⟩).lower ∧ (cell12312 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12312 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12312 ⟨43,by decide⟩).lower ∧ (cell12312 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12312 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12312 ⟨44,by decide⟩).lower ∧ (cell12312 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12312 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12312 ⟨45,by decide⟩).lower ∧ (cell12312 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12312 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12312 ⟨46,by decide⟩).lower ∧ (cell12312 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12312 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12312 ⟨47,by decide⟩).lower ∧ (cell12312 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12312 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12312 ⟨48,by decide⟩).lower ∧ (cell12312 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12312 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12312 ⟨49,by decide⟩).lower ∧ (cell12312 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12312 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12312 ⟨50,by decide⟩).lower ∧ (cell12312 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12312 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12312 ⟨51,by decide⟩).lower ∧ (cell12312 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12312 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12312 ⟨52,by decide⟩).lower ∧ (cell12312 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12312 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12312 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12312 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12312,cell12312,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12312 i).lower ∧
    (cell12312 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12312 i).upper ≤ (0.532 : ℝ) ∧
    (cell12312 i).centre ≤ (0.1 : ℝ) ∧ (cell12312 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12312 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12312 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12312

/-! The local source numeric instances at 12312 have no network premises. -/
namespace BstLean.Part264b.N12312
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12312 cell12312)

noncomputable def sourceNumerics12312 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12312 (cell12312 i)
      scalarRow12312.M scalarRow12312.H scalarRow12312.xi := by
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
    energy_allowance := scalarRow12312.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12312]
    centre_nonneg := (scalarRow12312.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12312]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12312
/-! Actual 12313 scalar aliases and the unchanged imported parallel allowance. -/
