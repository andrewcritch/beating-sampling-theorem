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
namespace BstLean.Part264b.N12313
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12313 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12313 12313 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12313.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12313 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12313 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12313 := gPlus_lower 12313
end BstLean.Part264b.N12313

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12313
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036372600702 : ℝ) ≤ wn 12313 := by
  have hn : √(12313 : ℝ) ≤ 110.963958112534 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12313 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.963958112534 ≤ 2 / √12313 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259938839 : ℝ) ≤ rhoBar 12313 BstLean.Part154.csC ∧
    rhoBar 12313 BstLean.Part154.csC ≤ 0.000259972449 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036372600702 : ℝ) / (1.295212 * 12313) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12313) := by gcongr
      _ ≤ (0.000259972449 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12313 BstLean.Part154.csC) ≤ 0.001039957382 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12313 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12313 BstLean.Part154.csC) (piBar (rhoBar 12313 BstLean.Part154.csC)) ≤ 0.000198569007 ∧
    cc1 (rhoBar 12313 BstLean.Part154.csC) (piBar (rhoBar 12313 BstLean.Part154.csC)) ≤ 0.000126350717 ∧
    cc2 (rhoBar 12313 BstLean.Part154.csC) ≤ 0.000073347485 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12313 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12313 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12313 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12313 BstLean.Part154.csC * nuR (rhoBar 12313 BstLean.Part154.csC)) ≤ 0.000519961795 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259972449 : ℝ) * 0.001039957382 := by gcongr
      _ ≤ (0.000519961795 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12313 BstLean.Part154.csC) * nuR (rhoBar 12313 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039957382 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12313 BstLean.Part154.csC) * rhoBar 12313 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259972449 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259972449 / 2 + 0.399 * 0.001039957382 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198569007 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519961795 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126350717 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259972449 / 1.414213562 := by gcongr
      _ ≤ (0.000073347485 : ℝ) := by norm_num

end BstLean.Part264b.N12313

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12313
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12313 BstLean.Part154.csC) (piBar (rhoBar 12313 BstLean.Part154.csC)) ≤ 1.70278E-7 := by
  have hr0 : 0 ≤ rhoBar 12313 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12313 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12313 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12313 BstLean.Part154.csC) (piBar (rhoBar 12313 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12313 BstLean.Part154.csC) (piBar (rhoBar 12313 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12313 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198569007 : ℝ) ^ 2 + 0.000126350717 ^ 2 + 3 * 0.000073347485 ^ 2 +
        2 * 0.797885 * 0.000198569007 * 0.000126350717 + 2 * 0.000198569007 * 0.000073347485 +
        4 * 0.797885 * 0.000126350717 * 0.000073347485 := by gcongr
    _ ≤ (1.70278E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12313 BstLean.Part154.csC Θ ≤ 0.002715931164 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12313 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12313 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12313 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12313 BstLean.Part154.csC) (piBar (rhoBar 12313 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12313 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70278E-7 / (0.000259938839 : ℝ) := by gcongr
    _ ≤ 0.002715931164 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12313 BstLean.Part154.csC Θ ≤ 0.003015104412 + 0.000686181384 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12313 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12313 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12313 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259972449 +
        (6863 / 10000) * 0.000259972449 * 12313 * 0.001039957382) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003015104412 + 0.000686181384 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12313 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12313 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12313 0.011 Θ ∧ gammaRatio 12313 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12313 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12313) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12313 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12313 0.011 Θ) :=
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
    badAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12313 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12313 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12313 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12313 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12313 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12313 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12313 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12313 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12313 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12313 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12313 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004115104412 + 0.003402112548 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12313

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12313
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12313 BstLean.Part154.csC) (piBar (rhoBar 12313 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12313 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12313 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12313 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12313 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12313 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12313 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12313 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12313 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12313 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12313 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12313 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12313 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053311740763 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12313) ≤ 0.010762391694 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12313 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010762391694 + 2 * 0.737676 / 12313) := by gcongr
    _ ≤ (0.053311740763 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12313 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12313

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12313
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485516933 : ℝ) ≤ plow 12313 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12313) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407813500)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425863862) : eMP 12313 0.011 xi bn ≤ 0.001226786928 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12313 : ℝ) * (1 - 0.011))) ≤ 0.000606504331 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001425863862 / (12313 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606504331 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606504331 : ℝ) + 3.141593 * 0.053407813500 / (12313 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001226786928 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407813500)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425863862) : PiBarMP 12313 12 0.011 xi bn ≤ 0.163800192133 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12313 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037760612575 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.351968718278 : ℝ) ≤ √((12313 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.963958112533 : ℝ) ≤ √12313 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12313) ≤ 0.125557960439 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037760612575 + 0.053407813500 * 1.772454 / (2 * (110.351968718278 : ℝ))) * (1 + 0.001226786928) +
        8 / (12313 * 110.963958112533) + 0.125557960439 := by gcongr
    _ ≤ (0.163800192133 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407813500)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425863862) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284413046472) :
    parallelOracle 12313 0.011 xi bn cd ≤ 0.164825036372 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12313 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12313 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485516933 : ℝ) ≤ plow 12313 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.963958112533 : ℝ) ≤ √12313 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284413046472 : ℝ) / (2 * 0.560485516933 * 110.963958112533)) * 0.163800192133 +
        0.284413046472 ^ 2 / (2 * 0.560485516933 * 110.963958112533) := by gcongr
    _ ≤ (0.164825036372 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407813500) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425863862)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284413046472) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12313 12313 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485516933 : ℝ) ≤ plow 12313 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.963958112533 : ℝ) ≤ √12313 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12313 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12313 Θ 1.22 ≤ 0.011950731775 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.963958112533 := by gcongr <;> linarith
      _ ≤ (0.011950731775 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12313 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12313 12313 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12313 12313 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12313 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12313 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12313 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12313 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164825036372 + 0.011950731775 + (0.008646 : ℝ) *
        (1 + 2 * (0.284413046472 + 0.011950731775) / (0.560485516933 * 110.963958112533))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12313]

end BstLean.Part264b.N12313

/-! The original eight local profiles supply actual 12313 moment certificates. -/
namespace BstLean.Part264b.N12313
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12313 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053407813500 ∧
    0 ≤ bN 12313 BstLean.Part154.csC (groupTheta g) ∧ bN 12313 BstLean.Part154.csC (groupTheta g) ≤ 0.001425863862 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12313 12313 0.011
      (momentAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12313 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12313 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12313 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231101305709 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12313 0.011
      (momentAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12313 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12313
/-! The actual computed-centre upper energy formula at 12313. -/
namespace BstLean.Part264b.N12313
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12313

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12313
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12313 cell12313)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086712112523
  | 2 => 0.087679567356
  | 3 => 0.088649116465
  | 4 => 0.089623060199
  | 5 => 0.090604146819
  | 6 => 0.091595634430
  | 7 => 0.092601357923
  | 8 => 0.093625800838
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12313 12313 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12313 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12313

/-! Actual upper energy certificates on all 43 source endpoints at 12313. -/
namespace BstLean.Part264b.N12313
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12313 cell12313)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12313 (gMinus 12313) (1 - (cell12313 i).lower) ≤ 1 ∧
    energyUpper 12313 (gMinus 12313) (BstLean.Part211.gPlus 12313)
      (finiteEnergy 12313 12313 0.011) (1 - (cell12313 i).lower) ≤
      (cell12313 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12313) (by norm_num)
        (q := 1 - (cell12313 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12313,cell12313]) (by norm_num [scalarRow12313,cell12313])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12313,cell12313])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12313

/-! Source-cell containment and simple scalar guards at 12313. -/
namespace BstLean.Part264b.N12313
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12313 cell12313)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12313 ⟨10,by decide⟩).lower ∧ (cell12313 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12313 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12313 ⟨11,by decide⟩).lower ∧ (cell12313 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12313 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12313 ⟨12,by decide⟩).lower ∧ (cell12313 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12313 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12313 ⟨13,by decide⟩).lower ∧ (cell12313 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12313 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12313 ⟨14,by decide⟩).lower ∧ (cell12313 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12313 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12313 ⟨15,by decide⟩).lower ∧ (cell12313 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12313 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12313 ⟨16,by decide⟩).lower ∧ (cell12313 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12313 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12313 ⟨17,by decide⟩).lower ∧ (cell12313 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12313 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12313 ⟨18,by decide⟩).lower ∧ (cell12313 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12313 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12313 ⟨19,by decide⟩).lower ∧ (cell12313 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12313 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12313 ⟨20,by decide⟩).lower ∧ (cell12313 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12313 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12313 ⟨21,by decide⟩).lower ∧ (cell12313 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12313 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12313 ⟨22,by decide⟩).lower ∧ (cell12313 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12313 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12313 ⟨23,by decide⟩).lower ∧ (cell12313 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12313 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12313 ⟨24,by decide⟩).lower ∧ (cell12313 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12313 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12313 ⟨25,by decide⟩).lower ∧ (cell12313 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12313 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12313 ⟨26,by decide⟩).lower ∧ (cell12313 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12313 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12313 ⟨27,by decide⟩).lower ∧ (cell12313 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12313 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12313 ⟨28,by decide⟩).lower ∧ (cell12313 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12313 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12313 ⟨29,by decide⟩).lower ∧ (cell12313 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12313 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12313 ⟨30,by decide⟩).lower ∧ (cell12313 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12313 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12313 ⟨31,by decide⟩).lower ∧ (cell12313 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12313 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12313 ⟨32,by decide⟩).lower ∧ (cell12313 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12313 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12313 ⟨33,by decide⟩).lower ∧ (cell12313 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12313 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12313 ⟨34,by decide⟩).lower ∧ (cell12313 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12313 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12313 ⟨35,by decide⟩).lower ∧ (cell12313 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12313 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12313 ⟨36,by decide⟩).lower ∧ (cell12313 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12313 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12313 ⟨37,by decide⟩).lower ∧ (cell12313 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12313 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12313 ⟨38,by decide⟩).lower ∧ (cell12313 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12313 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12313 ⟨39,by decide⟩).lower ∧ (cell12313 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12313 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12313 ⟨40,by decide⟩).lower ∧ (cell12313 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12313 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12313 ⟨41,by decide⟩).lower ∧ (cell12313 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12313 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12313 ⟨42,by decide⟩).lower ∧ (cell12313 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12313 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12313 ⟨43,by decide⟩).lower ∧ (cell12313 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12313 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12313 ⟨44,by decide⟩).lower ∧ (cell12313 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12313 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12313 ⟨45,by decide⟩).lower ∧ (cell12313 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12313 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12313 ⟨46,by decide⟩).lower ∧ (cell12313 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12313 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12313 ⟨47,by decide⟩).lower ∧ (cell12313 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12313 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12313 ⟨48,by decide⟩).lower ∧ (cell12313 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12313 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12313 ⟨49,by decide⟩).lower ∧ (cell12313 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12313 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12313 ⟨50,by decide⟩).lower ∧ (cell12313 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12313 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12313 ⟨51,by decide⟩).lower ∧ (cell12313 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12313 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12313 ⟨52,by decide⟩).lower ∧ (cell12313 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12313 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12313 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12313 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12313,cell12313,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12313 i).lower ∧
    (cell12313 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12313 i).upper ≤ (0.532 : ℝ) ∧
    (cell12313 i).centre ≤ (0.1 : ℝ) ∧ (cell12313 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12313 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12313 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12313

/-! The local source numeric instances at 12313 have no network premises. -/
namespace BstLean.Part264b.N12313
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12313 cell12313)

noncomputable def sourceNumerics12313 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12313 (cell12313 i)
      scalarRow12313.M scalarRow12313.H scalarRow12313.xi := by
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
    energy_allowance := scalarRow12313.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12313]
    centre_nonneg := (scalarRow12313.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12313]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12313
/-! Actual 12314 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12314
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12314 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12314 12314 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12314.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12314 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12314 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12314 := gPlus_lower 12314
end BstLean.Part264b.N12314

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12314
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036371110602 : ℝ) ≤ wn 12314 := by
  have hn : √(12314 : ℝ) ≤ 110.968463988649 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12314 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.968463988649 ≤ 2 / √12314 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259917356 : ℝ) ≤ rhoBar 12314 BstLean.Part154.csC ∧
    rhoBar 12314 BstLean.Part154.csC ≤ 0.000259951337 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036371110602 : ℝ) / (1.295212 * 12314) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12314) := by gcongr
      _ ≤ (0.000259951337 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12314 BstLean.Part154.csC) ≤ 0.001039872923 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12314 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12314 BstLean.Part154.csC) (piBar (rhoBar 12314 BstLean.Part154.csC)) ≤ 0.000198552881 ∧
    cc1 (rhoBar 12314 BstLean.Part154.csC) (piBar (rhoBar 12314 BstLean.Part154.csC)) ≤ 0.000126340456 ∧
    cc2 (rhoBar 12314 BstLean.Part154.csC) ≤ 0.000073341528 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12314 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12314 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12314 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12314 BstLean.Part154.csC * nuR (rhoBar 12314 BstLean.Part154.csC)) ≤ 0.000519919568 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259951337 : ℝ) * 0.001039872923 := by gcongr
      _ ≤ (0.000519919568 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12314 BstLean.Part154.csC) * nuR (rhoBar 12314 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039872923 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12314 BstLean.Part154.csC) * rhoBar 12314 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259951337 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259951337 / 2 + 0.399 * 0.001039872923 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198552881 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519919568 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126340456 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259951337 / 1.414213562 := by gcongr
      _ ≤ (0.000073341528 : ℝ) := by norm_num

end BstLean.Part264b.N12314

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12314
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12314 BstLean.Part154.csC) (piBar (rhoBar 12314 BstLean.Part154.csC)) ≤ 1.70250E-7 := by
  have hr0 : 0 ≤ rhoBar 12314 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12314 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12314 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12314 BstLean.Part154.csC) (piBar (rhoBar 12314 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12314 BstLean.Part154.csC) (piBar (rhoBar 12314 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12314 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198552881 : ℝ) ^ 2 + 0.000126340456 ^ 2 + 3 * 0.000073341528 ^ 2 +
        2 * 0.797885 * 0.000198552881 * 0.000126340456 + 2 * 0.000198552881 * 0.000073341528 +
        4 * 0.797885 * 0.000126340456 * 0.000073341528 := by gcongr
    _ ≤ (1.70250E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12314 BstLean.Part154.csC Θ ≤ 0.002715709008 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12314 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12314 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12314 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12314 BstLean.Part154.csC) (piBar (rhoBar 12314 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12314 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70250E-7 / (0.000259917356 : ℝ) := by gcongr
    _ ≤ 0.002715709008 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12314 BstLean.Part154.csC Θ ≤ 0.003014859543 + 0.000686125661 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12314 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12314 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12314 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259951337 +
        (6863 / 10000) * 0.000259951337 * 12314 * 0.001039872923) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003014859543 + 0.000686125661 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12314 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12314 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12314 0.011 Θ ∧ gammaRatio 12314 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12314 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12314) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12314 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12314 0.011 Θ) :=
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
    badAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12314 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12314 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12314 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12314 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12314 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12314 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12314 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12314 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12314 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12314 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12314 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004114859543 + 0.003401834669 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12314

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12314
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12314 BstLean.Part154.csC) (piBar (rhoBar 12314 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12314 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12314 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12314 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12314 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12314 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12314 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12314 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12314 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12314 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12314 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12314 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12314 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053309552206 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12314) ≤ 0.010761954687 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12314 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010761954687 + 2 * 0.737676 / 12314) := by gcongr
    _ ≤ (0.053309552206 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12314 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12314

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12314
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485565039 : ℝ) ≤ plow 12314 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12314) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407422745)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425747230) : eMP 12314 0.011 xi bn ≤ 0.001226686844 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12314 : ℝ) * (1 - 0.011))) ≤ 0.000606454899 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001425747230 / (12314 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606454899 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606454899 : ℝ) + 3.141593 * 0.053407422745 / (12314 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001226686844 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407422745)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425747230) : PiBarMP 12314 12 0.011 xi bn ≤ 0.163793522449 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12314 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037759068183 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.356449743546 : ℝ) ≤ √((12314 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.968463988648 : ℝ) ≤ √12314 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12314) ≤ 0.125552862156 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037759068183 + 0.053407422745 * 1.772454 / (2 * (110.356449743546 : ℝ))) * (1 + 0.001226686844) +
        8 / (12314 * 110.968463988648) + 0.125552862156 := by gcongr
    _ ≤ (0.163793522449 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407422745)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425747230) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284410012494) :
    parallelOracle 12314 0.011 xi bn cd ≤ 0.164818291868 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12314 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12314 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485565039 : ℝ) ≤ plow 12314 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.968463988648 : ℝ) ≤ √12314 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284410012494 : ℝ) / (2 * 0.560485565039 * 110.968463988648)) * 0.163793522449 +
        0.284410012494 ^ 2 / (2 * 0.560485565039 * 110.968463988648) := by gcongr
    _ ≤ (0.164818291868 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407422745) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425747230)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284410012494) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12314 12314 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485565039 : ℝ) ≤ plow 12314 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.968463988648 : ℝ) ≤ √12314 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12314 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12314 Θ 1.22 ≤ 0.011950246515 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.968463988648 := by gcongr <;> linarith
      _ ≤ (0.011950246515 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12314 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12314 12314 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12314 12314 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12314 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12314 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12314 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12314 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164818291868 + 0.011950246515 + (0.008646 : ℝ) *
        (1 + 2 * (0.284410012494 + 0.011950246515) / (0.560485565039 * 110.968463988648))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12314]

end BstLean.Part264b.N12314

/-! The original eight local profiles supply actual 12314 moment certificates. -/
namespace BstLean.Part264b.N12314
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12314 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053407422745 ∧
    0 ≤ bN 12314 BstLean.Part154.csC (groupTheta g) ∧ bN 12314 BstLean.Part154.csC (groupTheta g) ≤ 0.001425747230 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12314 12314 0.011
      (momentAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12314 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12314 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12314 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231100460288 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12314 0.011
      (momentAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12314 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12314
/-! The actual computed-centre upper energy formula at 12314. -/
namespace BstLean.Part264b.N12314
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12314

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12314
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12314 cell12314)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086708679687
  | 2 => 0.087676058573
  | 3 => 0.088645518694
  | 4 => 0.089619357565
  | 5 => 0.090600320146
  | 6 => 0.091591660715
  | 7 => 0.092597209759
  | 8 => 0.093621445781
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12314 12314 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12314 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12314

/-! Actual upper energy certificates on all 43 source endpoints at 12314. -/
namespace BstLean.Part264b.N12314
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12314 cell12314)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12314 (gMinus 12314) (1 - (cell12314 i).lower) ≤ 1 ∧
    energyUpper 12314 (gMinus 12314) (BstLean.Part211.gPlus 12314)
      (finiteEnergy 12314 12314 0.011) (1 - (cell12314 i).lower) ≤
      (cell12314 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12314) (by norm_num)
        (q := 1 - (cell12314 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12314,cell12314]) (by norm_num [scalarRow12314,cell12314])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12314,cell12314])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12314

/-! Source-cell containment and simple scalar guards at 12314. -/
namespace BstLean.Part264b.N12314
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12314 cell12314)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12314 ⟨10,by decide⟩).lower ∧ (cell12314 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12314 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12314 ⟨11,by decide⟩).lower ∧ (cell12314 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12314 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12314 ⟨12,by decide⟩).lower ∧ (cell12314 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12314 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12314 ⟨13,by decide⟩).lower ∧ (cell12314 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12314 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12314 ⟨14,by decide⟩).lower ∧ (cell12314 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12314 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12314 ⟨15,by decide⟩).lower ∧ (cell12314 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12314 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12314 ⟨16,by decide⟩).lower ∧ (cell12314 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12314 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12314 ⟨17,by decide⟩).lower ∧ (cell12314 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12314 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12314 ⟨18,by decide⟩).lower ∧ (cell12314 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12314 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12314 ⟨19,by decide⟩).lower ∧ (cell12314 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12314 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12314 ⟨20,by decide⟩).lower ∧ (cell12314 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12314 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12314 ⟨21,by decide⟩).lower ∧ (cell12314 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12314 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12314 ⟨22,by decide⟩).lower ∧ (cell12314 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12314 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12314 ⟨23,by decide⟩).lower ∧ (cell12314 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12314 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12314 ⟨24,by decide⟩).lower ∧ (cell12314 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12314 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12314 ⟨25,by decide⟩).lower ∧ (cell12314 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12314 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12314 ⟨26,by decide⟩).lower ∧ (cell12314 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12314 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12314 ⟨27,by decide⟩).lower ∧ (cell12314 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12314 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12314 ⟨28,by decide⟩).lower ∧ (cell12314 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12314 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12314 ⟨29,by decide⟩).lower ∧ (cell12314 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12314 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12314 ⟨30,by decide⟩).lower ∧ (cell12314 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12314 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12314 ⟨31,by decide⟩).lower ∧ (cell12314 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12314 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12314 ⟨32,by decide⟩).lower ∧ (cell12314 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12314 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12314 ⟨33,by decide⟩).lower ∧ (cell12314 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12314 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12314 ⟨34,by decide⟩).lower ∧ (cell12314 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12314 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12314 ⟨35,by decide⟩).lower ∧ (cell12314 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12314 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12314 ⟨36,by decide⟩).lower ∧ (cell12314 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12314 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12314 ⟨37,by decide⟩).lower ∧ (cell12314 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12314 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12314 ⟨38,by decide⟩).lower ∧ (cell12314 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12314 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12314 ⟨39,by decide⟩).lower ∧ (cell12314 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12314 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12314 ⟨40,by decide⟩).lower ∧ (cell12314 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12314 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12314 ⟨41,by decide⟩).lower ∧ (cell12314 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12314 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12314 ⟨42,by decide⟩).lower ∧ (cell12314 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12314 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12314 ⟨43,by decide⟩).lower ∧ (cell12314 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12314 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12314 ⟨44,by decide⟩).lower ∧ (cell12314 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12314 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12314 ⟨45,by decide⟩).lower ∧ (cell12314 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12314 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12314 ⟨46,by decide⟩).lower ∧ (cell12314 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12314 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12314 ⟨47,by decide⟩).lower ∧ (cell12314 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12314 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12314 ⟨48,by decide⟩).lower ∧ (cell12314 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12314 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12314 ⟨49,by decide⟩).lower ∧ (cell12314 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12314 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12314 ⟨50,by decide⟩).lower ∧ (cell12314 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12314 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12314 ⟨51,by decide⟩).lower ∧ (cell12314 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12314 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12314 ⟨52,by decide⟩).lower ∧ (cell12314 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12314 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12314 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12314 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12314,cell12314,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12314 i).lower ∧
    (cell12314 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12314 i).upper ≤ (0.532 : ℝ) ∧
    (cell12314 i).centre ≤ (0.1 : ℝ) ∧ (cell12314 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12314 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12314 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12314

/-! The local source numeric instances at 12314 have no network premises. -/
namespace BstLean.Part264b.N12314
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12314 cell12314)

noncomputable def sourceNumerics12314 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12314 (cell12314 i)
      scalarRow12314.M scalarRow12314.H scalarRow12314.xi := by
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
    energy_allowance := scalarRow12314.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12314]
    centre_nonneg := (scalarRow12314.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12314]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12314
/-! Actual 12315 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12315
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12315 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12315 12315 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12315.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12315 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12315 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12315 := gPlus_lower 12315
end BstLean.Part264b.N12315

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12315
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036369620684 : ℝ) ≤ wn 12315 := by
  have hn : √(12315 : ℝ) ≤ 110.972969681811 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12315 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.972969681811 ≤ 2 / √12315 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259895876 : ℝ) ≤ rhoBar 12315 BstLean.Part154.csC ∧
    rhoBar 12315 BstLean.Part154.csC ≤ 0.000259930229 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036369620684 : ℝ) / (1.295212 * 12315) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12315) := by gcongr
      _ ≤ (0.000259930229 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12315 BstLean.Part154.csC) ≤ 0.001039788480 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12315 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12315 BstLean.Part154.csC) (piBar (rhoBar 12315 BstLean.Part154.csC)) ≤ 0.000198536758 ∧
    cc1 (rhoBar 12315 BstLean.Part154.csC) (piBar (rhoBar 12315 BstLean.Part154.csC)) ≤ 0.000126330196 ∧
    cc2 (rhoBar 12315 BstLean.Part154.csC) ≤ 0.000073335573 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12315 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12315 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12315 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12315 BstLean.Part154.csC * nuR (rhoBar 12315 BstLean.Part154.csC)) ≤ 0.000519877349 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259930229 : ℝ) * 0.001039788480 := by gcongr
      _ ≤ (0.000519877349 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12315 BstLean.Part154.csC) * nuR (rhoBar 12315 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039788480 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12315 BstLean.Part154.csC) * rhoBar 12315 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259930229 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259930229 / 2 + 0.399 * 0.001039788480 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198536758 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519877349 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126330196 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259930229 / 1.414213562 := by gcongr
      _ ≤ (0.000073335573 : ℝ) := by norm_num

end BstLean.Part264b.N12315

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12315
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12315 BstLean.Part154.csC) (piBar (rhoBar 12315 BstLean.Part154.csC)) ≤ 1.70222E-7 := by
  have hr0 : 0 ≤ rhoBar 12315 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12315 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12315 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12315 BstLean.Part154.csC) (piBar (rhoBar 12315 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12315 BstLean.Part154.csC) (piBar (rhoBar 12315 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12315 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198536758 : ℝ) ^ 2 + 0.000126330196 ^ 2 + 3 * 0.000073335573 ^ 2 +
        2 * 0.797885 * 0.000198536758 * 0.000126330196 + 2 * 0.000198536758 * 0.000073335573 +
        4 * 0.797885 * 0.000126330196 * 0.000073335573 := by gcongr
    _ ≤ (1.70222E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12315 BstLean.Part154.csC Θ ≤ 0.002715486784 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12315 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12315 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12315 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12315 BstLean.Part154.csC) (piBar (rhoBar 12315 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12315 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70222E-7 / (0.000259895876 : ℝ) := by gcongr
    _ ≤ 0.002715486784 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12315 BstLean.Part154.csC Θ ≤ 0.003014614727 + 0.000686069947 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12315 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12315 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12315 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259930229 +
        (6863 / 10000) * 0.000259930229 * 12315 * 0.001039788480) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003014614727 + 0.000686069947 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12315 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12315 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12315 0.011 Θ ∧ gammaRatio 12315 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12315 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12315) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12315 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12315 0.011 Θ) :=
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
    badAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12315 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12315 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12315 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12315 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12315 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12315 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12315 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12315 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12315 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12315 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12315 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004114614727 + 0.003401556731 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12315

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12315
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12315 BstLean.Part154.csC) (piBar (rhoBar 12315 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12315 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12315 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12315 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12315 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12315 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12315 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12315 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12315 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12315 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12315 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12315 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12315 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053307363915 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12315) ≤ 0.010761517733 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12315 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010761517733 + 2 * 0.737676 / 12315) := by gcongr
    _ ≤ (0.053307363915 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12315 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12315

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12315
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485613138 : ℝ) ≤ plow 12315 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12315) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407032011)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425630562) : eMP 12315 0.011 xi bn ≤ 0.001226586753 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12315 : ℝ) * (1 - 0.011))) ≤ 0.000606405463 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001425630562 / (12315 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606405463 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606405463 : ℝ) + 3.141593 * 0.053407032011 / (12315 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001226586753 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407032011)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425630562) : PiBarMP 12315 12 0.011 xi bn ≤ 0.163786852848 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12315 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037757523251 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.360930586870 : ℝ) ≤ √((12315 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.972969681810 : ℝ) ≤ √12315 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12315) ≤ 0.125547764494 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037757523251 + 0.053407032011 * 1.772454 / (2 * (110.360930586870 : ℝ))) * (1 + 0.001226586753) +
        8 / (12315 * 110.972969681810) + 0.125547764494 := by gcongr
    _ ≤ (0.163786852848 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407032011)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425630562) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284406978824) :
    parallelOracle 12315 0.011 xi bn cd ≤ 0.164811547457 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12315 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12315 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485613138 : ℝ) ≤ plow 12315 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.972969681810 : ℝ) ≤ √12315 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284406978824 : ℝ) / (2 * 0.560485613138 * 110.972969681810)) * 0.163786852848 +
        0.284406978824 ^ 2 / (2 * 0.560485613138 * 110.972969681810) := by gcongr
    _ ≤ (0.164811547457 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053407032011) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425630562)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284406978824) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12315 12315 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485613138 : ℝ) ≤ plow 12315 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.972969681810 : ℝ) ≤ √12315 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12315 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12315 Θ 1.22 ≤ 0.011949761314 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.972969681810 := by gcongr <;> linarith
      _ ≤ (0.011949761314 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12315 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12315 12315 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12315 12315 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12315 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12315 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12315 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12315 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164811547457 + 0.011949761314 + (0.008646 : ℝ) *
        (1 + 2 * (0.284406978824 + 0.011949761314) / (0.560485613138 * 110.972969681810))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12315]

end BstLean.Part264b.N12315

/-! The original eight local profiles supply actual 12315 moment certificates. -/
namespace BstLean.Part264b.N12315
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12315 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053407032011 ∧
    0 ≤ bN 12315 BstLean.Part154.csC (groupTheta g) ∧ bN 12315 BstLean.Part154.csC (groupTheta g) ≤ 0.001425630562 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12315 12315 0.011
      (momentAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12315 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12315 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12315 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231099614909 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12315 0.011
      (momentAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12315 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12315
/-! The actual computed-centre upper energy formula at 12315. -/
namespace BstLean.Part264b.N12315
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12315

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12315
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12315 cell12315)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086705248486
  | 2 => 0.087672551498
  | 3 => 0.088641922721
  | 4 => 0.089615656841
  | 5 => 0.090596495518
  | 6 => 0.091587689209
  | 7 => 0.092593064002
  | 8 => 0.093617093366
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12315 12315 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12315 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12315

/-! Actual upper energy certificates on all 43 source endpoints at 12315. -/
namespace BstLean.Part264b.N12315
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12315 cell12315)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12315 (gMinus 12315) (1 - (cell12315 i).lower) ≤ 1 ∧
    energyUpper 12315 (gMinus 12315) (BstLean.Part211.gPlus 12315)
      (finiteEnergy 12315 12315 0.011) (1 - (cell12315 i).lower) ≤
      (cell12315 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12315) (by norm_num)
        (q := 1 - (cell12315 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12315,cell12315]) (by norm_num [scalarRow12315,cell12315])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12315,cell12315])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12315

/-! Source-cell containment and simple scalar guards at 12315. -/
namespace BstLean.Part264b.N12315
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12315 cell12315)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12315 ⟨10,by decide⟩).lower ∧ (cell12315 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12315 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12315 ⟨11,by decide⟩).lower ∧ (cell12315 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12315 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12315 ⟨12,by decide⟩).lower ∧ (cell12315 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12315 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12315 ⟨13,by decide⟩).lower ∧ (cell12315 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12315 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12315 ⟨14,by decide⟩).lower ∧ (cell12315 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12315 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12315 ⟨15,by decide⟩).lower ∧ (cell12315 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12315 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12315 ⟨16,by decide⟩).lower ∧ (cell12315 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12315 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12315 ⟨17,by decide⟩).lower ∧ (cell12315 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12315 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12315 ⟨18,by decide⟩).lower ∧ (cell12315 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12315 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12315 ⟨19,by decide⟩).lower ∧ (cell12315 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12315 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12315 ⟨20,by decide⟩).lower ∧ (cell12315 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12315 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12315 ⟨21,by decide⟩).lower ∧ (cell12315 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12315 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12315 ⟨22,by decide⟩).lower ∧ (cell12315 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12315 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12315 ⟨23,by decide⟩).lower ∧ (cell12315 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12315 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12315 ⟨24,by decide⟩).lower ∧ (cell12315 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12315 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12315 ⟨25,by decide⟩).lower ∧ (cell12315 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12315 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12315 ⟨26,by decide⟩).lower ∧ (cell12315 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12315 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12315 ⟨27,by decide⟩).lower ∧ (cell12315 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12315 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12315 ⟨28,by decide⟩).lower ∧ (cell12315 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12315 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12315 ⟨29,by decide⟩).lower ∧ (cell12315 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12315 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12315 ⟨30,by decide⟩).lower ∧ (cell12315 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12315 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12315 ⟨31,by decide⟩).lower ∧ (cell12315 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12315 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12315 ⟨32,by decide⟩).lower ∧ (cell12315 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12315 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12315 ⟨33,by decide⟩).lower ∧ (cell12315 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12315 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12315 ⟨34,by decide⟩).lower ∧ (cell12315 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12315 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12315 ⟨35,by decide⟩).lower ∧ (cell12315 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12315 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12315 ⟨36,by decide⟩).lower ∧ (cell12315 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12315 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12315 ⟨37,by decide⟩).lower ∧ (cell12315 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12315 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12315 ⟨38,by decide⟩).lower ∧ (cell12315 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12315 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12315 ⟨39,by decide⟩).lower ∧ (cell12315 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12315 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12315 ⟨40,by decide⟩).lower ∧ (cell12315 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12315 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12315 ⟨41,by decide⟩).lower ∧ (cell12315 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12315 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12315 ⟨42,by decide⟩).lower ∧ (cell12315 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12315 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12315 ⟨43,by decide⟩).lower ∧ (cell12315 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12315 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12315 ⟨44,by decide⟩).lower ∧ (cell12315 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12315 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12315 ⟨45,by decide⟩).lower ∧ (cell12315 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12315 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12315 ⟨46,by decide⟩).lower ∧ (cell12315 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12315 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12315 ⟨47,by decide⟩).lower ∧ (cell12315 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12315 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12315 ⟨48,by decide⟩).lower ∧ (cell12315 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12315 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12315 ⟨49,by decide⟩).lower ∧ (cell12315 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12315 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12315 ⟨50,by decide⟩).lower ∧ (cell12315 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12315 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12315 ⟨51,by decide⟩).lower ∧ (cell12315 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12315 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12315 ⟨52,by decide⟩).lower ∧ (cell12315 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12315 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12315 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12315 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12315,cell12315,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12315 i).lower ∧
    (cell12315 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12315 i).upper ≤ (0.532 : ℝ) ∧
    (cell12315 i).centre ≤ (0.1 : ℝ) ∧ (cell12315 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12315 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12315 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12315

/-! The local source numeric instances at 12315 have no network premises. -/
namespace BstLean.Part264b.N12315
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12315 cell12315)

noncomputable def sourceNumerics12315 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12315 (cell12315 i)
      scalarRow12315.M scalarRow12315.H scalarRow12315.xi := by
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
    energy_allowance := scalarRow12315.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12315]
    centre_nonneg := (scalarRow12315.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12315]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12315
/-! Actual 12316 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12316
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12316 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12316 12316 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12316.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12316 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12316 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12316 := gPlus_lower 12316
end BstLean.Part264b.N12316

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12316
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036368130949 : ℝ) ≤ wn 12316 := by
  have hn : √(12316 : ℝ) ≤ 110.977475192041 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12316 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.977475192041 ≤ 2 / √12316 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259874400 : ℝ) ≤ rhoBar 12316 BstLean.Part154.csC ∧
    rhoBar 12316 BstLean.Part154.csC ≤ 0.000259909123 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036368130949 : ℝ) / (1.295212 * 12316) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12316) := by gcongr
      _ ≤ (0.000259909123 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12316 BstLean.Part154.csC) ≤ 0.001039704045 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12316 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12316 BstLean.Part154.csC) (piBar (rhoBar 12316 BstLean.Part154.csC)) ≤ 0.000198520636 ∧
    cc1 (rhoBar 12316 BstLean.Part154.csC) (piBar (rhoBar 12316 BstLean.Part154.csC)) ≤ 0.000126319938 ∧
    cc2 (rhoBar 12316 BstLean.Part154.csC) ≤ 0.000073329618 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12316 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12316 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12316 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12316 BstLean.Part154.csC * nuR (rhoBar 12316 BstLean.Part154.csC)) ≤ 0.000519835134 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259909123 : ℝ) * 0.001039704045 := by gcongr
      _ ≤ (0.000519835134 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12316 BstLean.Part154.csC) * nuR (rhoBar 12316 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039704045 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12316 BstLean.Part154.csC) * rhoBar 12316 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259909123 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259909123 / 2 + 0.399 * 0.001039704045 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198520636 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519835134 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126319938 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259909123 / 1.414213562 := by gcongr
      _ ≤ (0.000073329618 : ℝ) := by norm_num

end BstLean.Part264b.N12316

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12316
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12316 BstLean.Part154.csC) (piBar (rhoBar 12316 BstLean.Part154.csC)) ≤ 1.70195E-7 := by
  have hr0 : 0 ≤ rhoBar 12316 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12316 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12316 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12316 BstLean.Part154.csC) (piBar (rhoBar 12316 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12316 BstLean.Part154.csC) (piBar (rhoBar 12316 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12316 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198520636 : ℝ) ^ 2 + 0.000126319938 ^ 2 + 3 * 0.000073329618 ^ 2 +
        2 * 0.797885 * 0.000198520636 * 0.000126319938 + 2 * 0.000198520636 * 0.000073329618 +
        4 * 0.797885 * 0.000126319938 * 0.000073329618 := by gcongr
    _ ≤ (1.70195E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12316 BstLean.Part154.csC Θ ≤ 0.002715280436 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12316 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12316 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12316 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12316 BstLean.Part154.csC) (piBar (rhoBar 12316 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12316 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70195E-7 / (0.000259874400 : ℝ) := by gcongr
    _ ≤ 0.002715280436 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12316 BstLean.Part154.csC Θ ≤ 0.003014369918 + 0.000686014239 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12316 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12316 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12316 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259909123 +
        (6863 / 10000) * 0.000259909123 * 12316 * 0.001039704045) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003014369918 + 0.000686014239 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12316 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12316 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12316 0.011 Θ ∧ gammaRatio 12316 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12316 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12316) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12316 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12316 0.011 Θ) :=
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
    badAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12316 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12316 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12316 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12316 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12316 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12316 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12316 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12316 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12316 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12316 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12316 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004114369918 + 0.003401294675 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12316

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12316
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12316 BstLean.Part154.csC) (piBar (rhoBar 12316 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12316 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12316 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12316 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12316 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12316 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12316 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12316 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12316 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12316 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12316 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12316 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12316 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053305175892 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12316) ≤ 0.010761080832 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12316 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010761080832 + 2 * 0.737676 / 12316) := by gcongr
    _ ≤ (0.053305175892 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12316 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12316

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12316
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485661229 : ℝ) ≤ plow 12316 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12316) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053406649623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425522229) : eMP 12316 0.011 xi bn ≤ 0.001226490218 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12316 : ℝ) * (1 - 0.011))) ≤ 0.000606357804 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001425522229 / (12316 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606357804 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606357804 : ℝ) + 3.141593 * 0.053406649623 / (12316 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001226490218 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053406649623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425522229) : PiBarMP 12316 12 0.011 xi bn ≤ 0.163780294525 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12316 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037756088635 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.365411248271 : ℝ) ≤ √((12316 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.977475192040 : ℝ) ≤ √12316 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12316) ≤ 0.125542667453 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037756088635 + 0.053406649623 * 1.772454 / (2 * (110.365411248271 : ℝ))) * (1 + 0.001226490218) +
        8 / (12316 * 110.977475192040) + 0.125542667453 := by gcongr
    _ ≤ (0.163780294525 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053406649623)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425522229) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284403963477) :
    parallelOracle 12316 0.011 xi bn cd ≤ 0.164804914694 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12316 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12316 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485661229 : ℝ) ≤ plow 12316 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.977475192040 : ℝ) ≤ √12316 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284403963477 : ℝ) / (2 * 0.560485661229 * 110.977475192040)) * 0.163780294525 +
        0.284403963477 ^ 2 / (2 * 0.560485661229 * 110.977475192040) := by gcongr
    _ ≤ (0.164804914694 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053406649623) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425522229)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284403963477) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12316 12316 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485661229 : ℝ) ≤ plow 12316 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.977475192040 : ℝ) ≤ √12316 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12316 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12316 Θ 1.22 ≤ 0.011949276173 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.977475192040 := by gcongr <;> linarith
      _ ≤ (0.011949276173 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12316 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12316 12316 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12316 12316 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12316 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12316 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12316 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12316 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164804914694 + 0.011949276173 + (0.008646 : ℝ) *
        (1 + 2 * (0.284403963477 + 0.011949276173) / (0.560485661229 * 110.977475192040))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12316]

end BstLean.Part264b.N12316

/-! The original eight local profiles supply actual 12316 moment certificates. -/
namespace BstLean.Part264b.N12316
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12316 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053406649623 ∧
    0 ≤ bN 12316 BstLean.Part154.csC (groupTheta g) ∧ bN 12316 BstLean.Part154.csC (groupTheta g) ≤ 0.001425522229 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12316 12316 0.011
      (momentAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12316 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12316 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12316 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231098787585 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12316 0.011
      (momentAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12316 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12316
/-! The actual computed-centre upper energy formula at 12316. -/
namespace BstLean.Part264b.N12316
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12316

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12316
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12316 cell12316)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086701818917
  | 2 => 0.087669046128
  | 3 => 0.088638328544
  | 4 => 0.089611958025
  | 5 => 0.090592672933
  | 6 => 0.091583719910
  | 7 => 0.092588920648
  | 8 => 0.093612743590
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12316 12316 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12316 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12316

/-! Actual upper energy certificates on all 43 source endpoints at 12316. -/
namespace BstLean.Part264b.N12316
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12316 cell12316)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12316 (gMinus 12316) (1 - (cell12316 i).lower) ≤ 1 ∧
    energyUpper 12316 (gMinus 12316) (BstLean.Part211.gPlus 12316)
      (finiteEnergy 12316 12316 0.011) (1 - (cell12316 i).lower) ≤
      (cell12316 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12316) (by norm_num)
        (q := 1 - (cell12316 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12316,cell12316]) (by norm_num [scalarRow12316,cell12316])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12316,cell12316])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12316

/-! Source-cell containment and simple scalar guards at 12316. -/
namespace BstLean.Part264b.N12316
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12316 cell12316)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12316 ⟨10,by decide⟩).lower ∧ (cell12316 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12316 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12316 ⟨11,by decide⟩).lower ∧ (cell12316 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12316 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12316 ⟨12,by decide⟩).lower ∧ (cell12316 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12316 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12316 ⟨13,by decide⟩).lower ∧ (cell12316 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12316 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12316 ⟨14,by decide⟩).lower ∧ (cell12316 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12316 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12316 ⟨15,by decide⟩).lower ∧ (cell12316 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12316 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12316 ⟨16,by decide⟩).lower ∧ (cell12316 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12316 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12316 ⟨17,by decide⟩).lower ∧ (cell12316 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12316 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12316 ⟨18,by decide⟩).lower ∧ (cell12316 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12316 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12316 ⟨19,by decide⟩).lower ∧ (cell12316 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12316 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12316 ⟨20,by decide⟩).lower ∧ (cell12316 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12316 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12316 ⟨21,by decide⟩).lower ∧ (cell12316 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12316 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12316 ⟨22,by decide⟩).lower ∧ (cell12316 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12316 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12316 ⟨23,by decide⟩).lower ∧ (cell12316 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12316 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12316 ⟨24,by decide⟩).lower ∧ (cell12316 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12316 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12316 ⟨25,by decide⟩).lower ∧ (cell12316 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12316 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12316 ⟨26,by decide⟩).lower ∧ (cell12316 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12316 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12316 ⟨27,by decide⟩).lower ∧ (cell12316 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12316 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12316 ⟨28,by decide⟩).lower ∧ (cell12316 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12316 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12316 ⟨29,by decide⟩).lower ∧ (cell12316 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12316 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12316 ⟨30,by decide⟩).lower ∧ (cell12316 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12316 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12316 ⟨31,by decide⟩).lower ∧ (cell12316 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12316 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12316 ⟨32,by decide⟩).lower ∧ (cell12316 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12316 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12316 ⟨33,by decide⟩).lower ∧ (cell12316 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12316 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12316 ⟨34,by decide⟩).lower ∧ (cell12316 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12316 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12316 ⟨35,by decide⟩).lower ∧ (cell12316 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12316 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12316 ⟨36,by decide⟩).lower ∧ (cell12316 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12316 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12316 ⟨37,by decide⟩).lower ∧ (cell12316 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12316 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12316 ⟨38,by decide⟩).lower ∧ (cell12316 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12316 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12316 ⟨39,by decide⟩).lower ∧ (cell12316 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12316 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12316 ⟨40,by decide⟩).lower ∧ (cell12316 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12316 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12316 ⟨41,by decide⟩).lower ∧ (cell12316 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12316 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12316 ⟨42,by decide⟩).lower ∧ (cell12316 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12316 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12316 ⟨43,by decide⟩).lower ∧ (cell12316 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12316 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12316 ⟨44,by decide⟩).lower ∧ (cell12316 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12316 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12316 ⟨45,by decide⟩).lower ∧ (cell12316 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12316 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12316 ⟨46,by decide⟩).lower ∧ (cell12316 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12316 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12316 ⟨47,by decide⟩).lower ∧ (cell12316 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12316 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12316 ⟨48,by decide⟩).lower ∧ (cell12316 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12316 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12316 ⟨49,by decide⟩).lower ∧ (cell12316 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12316 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12316 ⟨50,by decide⟩).lower ∧ (cell12316 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12316 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12316 ⟨51,by decide⟩).lower ∧ (cell12316 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12316 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12316 ⟨52,by decide⟩).lower ∧ (cell12316 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12316 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12316 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12316 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12316,cell12316,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12316 i).lower ∧
    (cell12316 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12316 i).upper ≤ (0.532 : ℝ) ∧
    (cell12316 i).centre ≤ (0.1 : ℝ) ∧ (cell12316 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12316 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12316 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12316

/-! The local source numeric instances at 12316 have no network premises. -/
namespace BstLean.Part264b.N12316
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12316 cell12316)

noncomputable def sourceNumerics12316 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12316 (cell12316 i)
      scalarRow12316.M scalarRow12316.H scalarRow12316.xi := by
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
    energy_allowance := scalarRow12316.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12316]
    centre_nonneg := (scalarRow12316.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12316]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12316
/-! Actual 12317 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12317
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12317 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12317 12317 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12317.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12317 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12317 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12317 := gPlus_lower 12317
end BstLean.Part264b.N12317

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12317
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036366641396 : ℝ) ≤ wn 12317 := by
  have hn : √(12317 : ℝ) ≤ 110.981980519362 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12317 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.981980519362 ≤ 2 / √12317 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259852928 : ℝ) ≤ rhoBar 12317 BstLean.Part154.csC ∧
    rhoBar 12317 BstLean.Part154.csC ≤ 0.000259888022 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036366641396 : ℝ) / (1.295212 * 12317) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12317) := by gcongr
      _ ≤ (0.000259888022 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12317 BstLean.Part154.csC) ≤ 0.001039619630 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12317 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12317 BstLean.Part154.csC) (piBar (rhoBar 12317 BstLean.Part154.csC)) ≤ 0.000198504518 ∧
    cc1 (rhoBar 12317 BstLean.Part154.csC) (piBar (rhoBar 12317 BstLean.Part154.csC)) ≤ 0.000126309682 ∧
    cc2 (rhoBar 12317 BstLean.Part154.csC) ≤ 0.000073323665 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12317 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12317 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12317 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12317 BstLean.Part154.csC * nuR (rhoBar 12317 BstLean.Part154.csC)) ≤ 0.000519792930 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259888022 : ℝ) * 0.001039619630 := by gcongr
      _ ≤ (0.000519792930 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12317 BstLean.Part154.csC) * nuR (rhoBar 12317 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039619630 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12317 BstLean.Part154.csC) * rhoBar 12317 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259888022 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259888022 / 2 + 0.399 * 0.001039619630 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198504518 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519792930 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126309682 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259888022 / 1.414213562 := by gcongr
      _ ≤ (0.000073323665 : ℝ) := by norm_num

end BstLean.Part264b.N12317

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12317
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12317 BstLean.Part154.csC) (piBar (rhoBar 12317 BstLean.Part154.csC)) ≤ 1.70167E-7 := by
  have hr0 : 0 ≤ rhoBar 12317 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12317 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12317 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12317 BstLean.Part154.csC) (piBar (rhoBar 12317 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12317 BstLean.Part154.csC) (piBar (rhoBar 12317 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12317 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198504518 : ℝ) ^ 2 + 0.000126309682 ^ 2 + 3 * 0.000073323665 ^ 2 +
        2 * 0.797885 * 0.000198504518 * 0.000126309682 + 2 * 0.000198504518 * 0.000073323665 +
        4 * 0.797885 * 0.000126309682 * 0.000073323665 := by gcongr
    _ ≤ (1.70167E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12317 BstLean.Part154.csC Θ ≤ 0.002715058056 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12317 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12317 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12317 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12317 BstLean.Part154.csC) (piBar (rhoBar 12317 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12317 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70167E-7 / (0.000259852928 : ℝ) := by gcongr
    _ ≤ 0.002715058056 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12317 BstLean.Part154.csC Θ ≤ 0.003014125185 + 0.000685958544 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12317 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12317 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12317 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259888022 +
        (6863 / 10000) * 0.000259888022 * 12317 * 0.001039619630) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003014125185 + 0.000685958544 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12317 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12317 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12317 0.011 Θ ∧ gammaRatio 12317 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12317 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12317) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12317 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12317 0.011 Θ) :=
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
    badAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12317 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12317 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12317 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12317 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12317 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12317 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12317 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12317 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12317 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12317 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12317 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004114125185 + 0.003401016600 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12317

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12317
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12317 BstLean.Part154.csC) (piBar (rhoBar 12317 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12317 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12317 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12317 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12317 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12317 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12317 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12317 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12317 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12317 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12317 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12317 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12317 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053302988141 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12317) ≤ 0.010760643985 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12317 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010760643985 + 2 * 0.737676 / 12317) := by gcongr
    _ ≤ (0.053302988141 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12317 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12317

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12317
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485709312 : ℝ) ≤ plow 12317 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12317) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053406258900)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425405480) : eMP 12317 0.011 xi bn ≤ 0.001226390110 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12317 : ℝ) * (1 - 0.011))) ≤ 0.000606308360 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001425405480 / (12317 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606308360 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606308360 : ℝ) + 3.141593 * 0.053406258900 / (12317 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001226390110 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053406258900)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425405480) : PiBarMP 12317 12 0.011 xi bn ≤ 0.163773624976 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12317 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037754542509 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.369891727771 : ℝ) ≤ √((12317 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.981980519361 : ℝ) ≤ √12317 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12317) ≤ 0.125537571033 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037754542509 + 0.053406258900 * 1.772454 / (2 * (110.369891727771 : ℝ))) * (1 + 0.001226390110) +
        8 / (12317 * 110.981980519361) + 0.125537571033 := by gcongr
    _ ≤ (0.163773624976 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053406258900)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425405480) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284400930365) :
    parallelOracle 12317 0.011 xi bn cd ≤ 0.164798170355 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12317 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12317 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485709312 : ℝ) ≤ plow 12317 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.981980519361 : ℝ) ≤ √12317 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284400930365 : ℝ) / (2 * 0.560485709312 * 110.981980519361)) * 0.163773624976 +
        0.284400930365 ^ 2 / (2 * 0.560485709312 * 110.981980519361) := by gcongr
    _ ≤ (0.164798170355 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053406258900) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425405480)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284400930365) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12317 12317 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485709312 : ℝ) ≤ plow 12317 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.981980519361 : ℝ) ≤ √12317 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12317 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12317 Θ 1.22 ≤ 0.011948791091 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.981980519361 := by gcongr <;> linarith
      _ ≤ (0.011948791091 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12317 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12317 12317 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12317 12317 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12317 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12317 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12317 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12317 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164798170355 + 0.011948791091 + (0.008646 : ℝ) *
        (1 + 2 * (0.284400930365 + 0.011948791091) / (0.560485709312 * 110.981980519361))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12317]

end BstLean.Part264b.N12317

/-! The original eight local profiles supply actual 12317 moment certificates. -/
namespace BstLean.Part264b.N12317
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12317 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053406258900 ∧
    0 ≤ bN 12317 BstLean.Part154.csC (groupTheta g) ∧ bN 12317 BstLean.Part154.csC (groupTheta g) ≤ 0.001425405480 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12317 12317 0.011
      (momentAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12317 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12317 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12317 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231097942224 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12317 0.011
      (momentAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12317 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12317
/-! The actual computed-centre upper energy formula at 12317. -/
namespace BstLean.Part264b.N12317
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12317

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12317
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12317 cell12317)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086698390978
  | 2 => 0.087665542463
  | 3 => 0.088634736163
  | 4 => 0.089608261114
  | 5 => 0.090588852389
  | 6 => 0.091579752814
  | 7 => 0.092584779694
  | 8 => 0.093608396449
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12317 12317 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12317 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12317

/-! Actual upper energy certificates on all 43 source endpoints at 12317. -/
namespace BstLean.Part264b.N12317
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12317 cell12317)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12317 (gMinus 12317) (1 - (cell12317 i).lower) ≤ 1 ∧
    energyUpper 12317 (gMinus 12317) (BstLean.Part211.gPlus 12317)
      (finiteEnergy 12317 12317 0.011) (1 - (cell12317 i).lower) ≤
      (cell12317 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12317) (by norm_num)
        (q := 1 - (cell12317 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12317,cell12317]) (by norm_num [scalarRow12317,cell12317])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12317,cell12317])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12317

/-! Source-cell containment and simple scalar guards at 12317. -/
namespace BstLean.Part264b.N12317
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12317 cell12317)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12317 ⟨10,by decide⟩).lower ∧ (cell12317 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12317 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12317 ⟨11,by decide⟩).lower ∧ (cell12317 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12317 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12317 ⟨12,by decide⟩).lower ∧ (cell12317 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12317 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12317 ⟨13,by decide⟩).lower ∧ (cell12317 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12317 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12317 ⟨14,by decide⟩).lower ∧ (cell12317 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12317 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12317 ⟨15,by decide⟩).lower ∧ (cell12317 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12317 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12317 ⟨16,by decide⟩).lower ∧ (cell12317 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12317 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12317 ⟨17,by decide⟩).lower ∧ (cell12317 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12317 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12317 ⟨18,by decide⟩).lower ∧ (cell12317 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12317 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12317 ⟨19,by decide⟩).lower ∧ (cell12317 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12317 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12317 ⟨20,by decide⟩).lower ∧ (cell12317 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12317 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12317 ⟨21,by decide⟩).lower ∧ (cell12317 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12317 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12317 ⟨22,by decide⟩).lower ∧ (cell12317 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12317 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12317 ⟨23,by decide⟩).lower ∧ (cell12317 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12317 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12317 ⟨24,by decide⟩).lower ∧ (cell12317 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12317 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12317 ⟨25,by decide⟩).lower ∧ (cell12317 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12317 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12317 ⟨26,by decide⟩).lower ∧ (cell12317 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12317 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12317 ⟨27,by decide⟩).lower ∧ (cell12317 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12317 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12317 ⟨28,by decide⟩).lower ∧ (cell12317 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12317 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12317 ⟨29,by decide⟩).lower ∧ (cell12317 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12317 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12317 ⟨30,by decide⟩).lower ∧ (cell12317 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12317 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12317 ⟨31,by decide⟩).lower ∧ (cell12317 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12317 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12317 ⟨32,by decide⟩).lower ∧ (cell12317 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12317 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12317 ⟨33,by decide⟩).lower ∧ (cell12317 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12317 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12317 ⟨34,by decide⟩).lower ∧ (cell12317 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12317 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12317 ⟨35,by decide⟩).lower ∧ (cell12317 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12317 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12317 ⟨36,by decide⟩).lower ∧ (cell12317 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12317 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12317 ⟨37,by decide⟩).lower ∧ (cell12317 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12317 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12317 ⟨38,by decide⟩).lower ∧ (cell12317 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12317 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12317 ⟨39,by decide⟩).lower ∧ (cell12317 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12317 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12317 ⟨40,by decide⟩).lower ∧ (cell12317 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12317 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12317 ⟨41,by decide⟩).lower ∧ (cell12317 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12317 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12317 ⟨42,by decide⟩).lower ∧ (cell12317 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12317 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12317 ⟨43,by decide⟩).lower ∧ (cell12317 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12317 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12317 ⟨44,by decide⟩).lower ∧ (cell12317 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12317 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12317 ⟨45,by decide⟩).lower ∧ (cell12317 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12317 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12317 ⟨46,by decide⟩).lower ∧ (cell12317 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12317 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12317 ⟨47,by decide⟩).lower ∧ (cell12317 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12317 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12317 ⟨48,by decide⟩).lower ∧ (cell12317 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12317 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12317 ⟨49,by decide⟩).lower ∧ (cell12317 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12317 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12317 ⟨50,by decide⟩).lower ∧ (cell12317 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12317 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12317 ⟨51,by decide⟩).lower ∧ (cell12317 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12317 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12317 ⟨52,by decide⟩).lower ∧ (cell12317 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12317 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12317 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12317 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12317,cell12317,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12317 i).lower ∧
    (cell12317 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12317 i).upper ≤ (0.532 : ℝ) ∧
    (cell12317 i).centre ≤ (0.1 : ℝ) ∧ (cell12317 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12317 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12317 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12317

/-! The local source numeric instances at 12317 have no network premises. -/
namespace BstLean.Part264b.N12317
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12317 cell12317)

noncomputable def sourceNumerics12317 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12317 (cell12317 i)
      scalarRow12317.M scalarRow12317.H scalarRow12317.xi := by
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
    energy_allowance := scalarRow12317.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12317]
    centre_nonneg := (scalarRow12317.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12317]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12317
/-! Actual 12318 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12318
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12318 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12318 12318 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12318.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12318 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12318 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12318 := gPlus_lower 12318
end BstLean.Part264b.N12318

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12318
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036365152025 : ℝ) ≤ wn 12318 := by
  have hn : √(12318 : ℝ) ≤ 110.986485663797 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12318 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.986485663797 ≤ 2 / √12318 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259831459 : ℝ) ≤ rhoBar 12318 BstLean.Part154.csC ∧
    rhoBar 12318 BstLean.Part154.csC ≤ 0.000259866924 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036365152025 : ℝ) / (1.295212 * 12318) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12318) := by gcongr
      _ ≤ (0.000259866924 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12318 BstLean.Part154.csC) ≤ 0.001039535227 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12318 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12318 BstLean.Part154.csC) (piBar (rhoBar 12318 BstLean.Part154.csC)) ≤ 0.000198488402 ∧
    cc1 (rhoBar 12318 BstLean.Part154.csC) (piBar (rhoBar 12318 BstLean.Part154.csC)) ≤ 0.000126299428 ∧
    cc2 (rhoBar 12318 BstLean.Part154.csC) ≤ 0.000073317713 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12318 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12318 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12318 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12318 BstLean.Part154.csC * nuR (rhoBar 12318 BstLean.Part154.csC)) ≤ 0.000519750731 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259866924 : ℝ) * 0.001039535227 := by gcongr
      _ ≤ (0.000519750731 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12318 BstLean.Part154.csC) * nuR (rhoBar 12318 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039535227 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12318 BstLean.Part154.csC) * rhoBar 12318 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259866924 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259866924 / 2 + 0.399 * 0.001039535227 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198488402 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519750731 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126299428 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259866924 / 1.414213562 := by gcongr
      _ ≤ (0.000073317713 : ℝ) := by norm_num

end BstLean.Part264b.N12318

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12318
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12318 BstLean.Part154.csC) (piBar (rhoBar 12318 BstLean.Part154.csC)) ≤ 1.70140E-7 := by
  have hr0 : 0 ≤ rhoBar 12318 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12318 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12318 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12318 BstLean.Part154.csC) (piBar (rhoBar 12318 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12318 BstLean.Part154.csC) (piBar (rhoBar 12318 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12318 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198488402 : ℝ) ^ 2 + 0.000126299428 ^ 2 + 3 * 0.000073317713 ^ 2 +
        2 * 0.797885 * 0.000198488402 * 0.000126299428 + 2 * 0.000198488402 * 0.000073317713 +
        4 * 0.797885 * 0.000126299428 * 0.000073317713 := by gcongr
    _ ≤ (1.70140E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12318 BstLean.Part154.csC Θ ≤ 0.002714851564 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12318 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12318 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12318 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12318 BstLean.Part154.csC) (piBar (rhoBar 12318 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12318 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70140E-7 / (0.000259831459 : ℝ) := by gcongr
    _ ≤ 0.002714851564 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12318 BstLean.Part154.csC Θ ≤ 0.003013880481 + 0.000685902858 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12318 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12318 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12318 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259866924 +
        (6863 / 10000) * 0.000259866924 * 12318 * 0.001039535227) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003013880481 + 0.000685902858 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12318 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12318 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12318 0.011 Θ ∧ gammaRatio 12318 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12318 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12318) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12318 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12318 0.011 Θ) :=
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
    badAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12318 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12318 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12318 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12318 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12318 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12318 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12318 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12318 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12318 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12318 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12318 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004113880481 + 0.003400754422 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12318

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12318
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12318 BstLean.Part154.csC) (piBar (rhoBar 12318 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12318 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12318 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12318 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12318 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12318 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12318 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12318 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12318 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12318 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12318 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12318 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12318 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053300800658 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12318) ≤ 0.010760207191 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12318 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010760207191 + 2 * 0.737676 / 12318) := by gcongr
    _ ≤ (0.053300800658 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12318 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12318

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12318
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485757387 : ℝ) ≤ plow 12318 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12318) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405876553)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425297072) : eMP 12318 0.011 xi bn ≤ 0.001226293560 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12318 : ℝ) * (1 - 0.011))) ≤ 0.000606260693 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001425297072 / (12318 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606260693 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606260693 : ℝ) + 3.141593 * 0.053405876553 / (12318 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001226293560 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405876553)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425297072) : PiBarMP 12318 12 0.011 xi bn ≤ 0.163767066792 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12318 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037753106787 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.374372025393 : ℝ) ≤ √((12318 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.986485663796 : ℝ) ≤ √12318 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12318) ≤ 0.125532475233 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037753106787 + 0.053405876553 * 1.772454 / (2 * (110.374372025393 : ℝ))) * (1 + 0.001226293560) +
        8 / (12318 * 110.986485663796) + 0.125532475233 := by gcongr
    _ ≤ (0.163767066792 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405876553)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425297072) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284397915640) :
    parallelOracle 12318 0.011 xi bn cd ≤ 0.164791537752 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12318 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12318 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485757387 : ℝ) ≤ plow 12318 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.986485663796 : ℝ) ≤ √12318 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284397915640 : ℝ) / (2 * 0.560485757387 * 110.986485663796)) * 0.163767066792 +
        0.284397915640 ^ 2 / (2 * 0.560485757387 * 110.986485663796) := by gcongr
    _ ≤ (0.164791537752 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405876553) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425297072)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284397915640) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12318 12318 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485757387 : ℝ) ≤ plow 12318 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.986485663796 : ℝ) ≤ √12318 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12318 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12318 Θ 1.22 ≤ 0.011948306067 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.986485663796 := by gcongr <;> linarith
      _ ≤ (0.011948306067 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12318 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12318 12318 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12318 12318 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12318 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12318 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12318 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12318 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164791537752 + 0.011948306067 + (0.008646 : ℝ) *
        (1 + 2 * (0.284397915640 + 0.011948306067) / (0.560485757387 * 110.986485663796))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12318]

end BstLean.Part264b.N12318

/-! The original eight local profiles supply actual 12318 moment certificates. -/
namespace BstLean.Part264b.N12318
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12318 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053405876553 ∧
    0 ≤ bN 12318 BstLean.Part154.csC (groupTheta g) ∧ bN 12318 BstLean.Part154.csC (groupTheta g) ≤ 0.001425297072 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12318 12318 0.011
      (momentAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12318 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12318 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12318 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231097114982 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12318 0.011
      (momentAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12318 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12318
/-! The actual computed-centre upper energy formula at 12318. -/
namespace BstLean.Part264b.N12318
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12318

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12318
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12318 cell12318)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086694964667
  | 2 => 0.087662040500
  | 3 => 0.088631145574
  | 4 => 0.089604566107
  | 5 => 0.090585033883
  | 6 => 0.091575787921
  | 7 => 0.092580641139
  | 8 => 0.093604051941
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12318 12318 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12318 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12318

/-! Actual upper energy certificates on all 43 source endpoints at 12318. -/
namespace BstLean.Part264b.N12318
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12318 cell12318)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12318 (gMinus 12318) (1 - (cell12318 i).lower) ≤ 1 ∧
    energyUpper 12318 (gMinus 12318) (BstLean.Part211.gPlus 12318)
      (finiteEnergy 12318 12318 0.011) (1 - (cell12318 i).lower) ≤
      (cell12318 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12318) (by norm_num)
        (q := 1 - (cell12318 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12318,cell12318]) (by norm_num [scalarRow12318,cell12318])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12318,cell12318])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12318

/-! Source-cell containment and simple scalar guards at 12318. -/
namespace BstLean.Part264b.N12318
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12318 cell12318)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12318 ⟨10,by decide⟩).lower ∧ (cell12318 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12318 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12318 ⟨11,by decide⟩).lower ∧ (cell12318 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12318 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12318 ⟨12,by decide⟩).lower ∧ (cell12318 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12318 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12318 ⟨13,by decide⟩).lower ∧ (cell12318 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12318 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12318 ⟨14,by decide⟩).lower ∧ (cell12318 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12318 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12318 ⟨15,by decide⟩).lower ∧ (cell12318 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12318 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12318 ⟨16,by decide⟩).lower ∧ (cell12318 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12318 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12318 ⟨17,by decide⟩).lower ∧ (cell12318 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12318 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12318 ⟨18,by decide⟩).lower ∧ (cell12318 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12318 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12318 ⟨19,by decide⟩).lower ∧ (cell12318 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12318 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12318 ⟨20,by decide⟩).lower ∧ (cell12318 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12318 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12318 ⟨21,by decide⟩).lower ∧ (cell12318 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12318 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12318 ⟨22,by decide⟩).lower ∧ (cell12318 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12318 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12318 ⟨23,by decide⟩).lower ∧ (cell12318 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12318 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12318 ⟨24,by decide⟩).lower ∧ (cell12318 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12318 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12318 ⟨25,by decide⟩).lower ∧ (cell12318 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12318 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12318 ⟨26,by decide⟩).lower ∧ (cell12318 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12318 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12318 ⟨27,by decide⟩).lower ∧ (cell12318 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12318 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12318 ⟨28,by decide⟩).lower ∧ (cell12318 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12318 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12318 ⟨29,by decide⟩).lower ∧ (cell12318 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12318 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12318 ⟨30,by decide⟩).lower ∧ (cell12318 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12318 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12318 ⟨31,by decide⟩).lower ∧ (cell12318 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12318 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12318 ⟨32,by decide⟩).lower ∧ (cell12318 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12318 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12318 ⟨33,by decide⟩).lower ∧ (cell12318 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12318 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12318 ⟨34,by decide⟩).lower ∧ (cell12318 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12318 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12318 ⟨35,by decide⟩).lower ∧ (cell12318 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12318 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12318 ⟨36,by decide⟩).lower ∧ (cell12318 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12318 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12318 ⟨37,by decide⟩).lower ∧ (cell12318 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12318 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12318 ⟨38,by decide⟩).lower ∧ (cell12318 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12318 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12318 ⟨39,by decide⟩).lower ∧ (cell12318 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12318 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12318 ⟨40,by decide⟩).lower ∧ (cell12318 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12318 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12318 ⟨41,by decide⟩).lower ∧ (cell12318 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12318 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12318 ⟨42,by decide⟩).lower ∧ (cell12318 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12318 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12318 ⟨43,by decide⟩).lower ∧ (cell12318 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12318 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12318 ⟨44,by decide⟩).lower ∧ (cell12318 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12318 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12318 ⟨45,by decide⟩).lower ∧ (cell12318 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12318 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12318 ⟨46,by decide⟩).lower ∧ (cell12318 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12318 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12318 ⟨47,by decide⟩).lower ∧ (cell12318 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12318 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12318 ⟨48,by decide⟩).lower ∧ (cell12318 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12318 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12318 ⟨49,by decide⟩).lower ∧ (cell12318 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12318 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12318 ⟨50,by decide⟩).lower ∧ (cell12318 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12318 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12318 ⟨51,by decide⟩).lower ∧ (cell12318 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12318 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12318 ⟨52,by decide⟩).lower ∧ (cell12318 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12318 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12318 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12318 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12318,cell12318,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12318 i).lower ∧
    (cell12318 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12318 i).upper ≤ (0.532 : ℝ) ∧
    (cell12318 i).centre ≤ (0.1 : ℝ) ∧ (cell12318 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12318 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12318 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12318

/-! The local source numeric instances at 12318 have no network premises. -/
namespace BstLean.Part264b.N12318
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12318 cell12318)

noncomputable def sourceNumerics12318 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12318 (cell12318 i)
      scalarRow12318.M scalarRow12318.H scalarRow12318.xi := by
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
    energy_allowance := scalarRow12318.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12318]
    centre_nonneg := (scalarRow12318.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12318]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12318
/-! Actual 12319 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12319
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12319 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12319 12319 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12319.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12319 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12319 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12319 := gPlus_lower 12319
end BstLean.Part264b.N12319

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12319
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036363662838 : ℝ) ≤ wn 12319 := by
  have hn : √(12319 : ℝ) ≤ 110.990990625366 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12319 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.990990625366 ≤ 2 / √12319 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259809994 : ℝ) ≤ rhoBar 12319 BstLean.Part154.csC ∧
    rhoBar 12319 BstLean.Part154.csC ≤ 0.000259845829 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036363662838 : ℝ) / (1.295212 * 12319) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12319) := by gcongr
      _ ≤ (0.000259845829 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12319 BstLean.Part154.csC) ≤ 0.001039450836 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12319 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12319 BstLean.Part154.csC) (piBar (rhoBar 12319 BstLean.Part154.csC)) ≤ 0.000198472289 ∧
    cc1 (rhoBar 12319 BstLean.Part154.csC) (piBar (rhoBar 12319 BstLean.Part154.csC)) ≤ 0.000126289175 ∧
    cc2 (rhoBar 12319 BstLean.Part154.csC) ≤ 0.000073311761 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12319 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12319 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12319 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12319 BstLean.Part154.csC * nuR (rhoBar 12319 BstLean.Part154.csC)) ≤ 0.000519708538 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259845829 : ℝ) * 0.001039450836 := by gcongr
      _ ≤ (0.000519708538 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12319 BstLean.Part154.csC) * nuR (rhoBar 12319 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039450836 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12319 BstLean.Part154.csC) * rhoBar 12319 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259845829 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259845829 / 2 + 0.399 * 0.001039450836 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198472289 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519708538 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126289175 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259845829 / 1.414213562 := by gcongr
      _ ≤ (0.000073311761 : ℝ) := by norm_num

end BstLean.Part264b.N12319

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12319
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12319 BstLean.Part154.csC) (piBar (rhoBar 12319 BstLean.Part154.csC)) ≤ 1.70112E-7 := by
  have hr0 : 0 ≤ rhoBar 12319 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12319 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12319 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12319 BstLean.Part154.csC) (piBar (rhoBar 12319 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12319 BstLean.Part154.csC) (piBar (rhoBar 12319 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12319 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198472289 : ℝ) ^ 2 + 0.000126289175 ^ 2 + 3 * 0.000073311761 ^ 2 +
        2 * 0.797885 * 0.000198472289 * 0.000126289175 + 2 * 0.000198472289 * 0.000073311761 +
        4 * 0.797885 * 0.000126289175 * 0.000073311761 := by gcongr
    _ ≤ (1.70112E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12319 BstLean.Part154.csC Θ ≤ 0.002714629039 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12319 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12319 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12319 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12319 BstLean.Part154.csC) (piBar (rhoBar 12319 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12319 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70112E-7 / (0.000259809994 : ℝ) := by gcongr
    _ ≤ 0.002714629039 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12319 BstLean.Part154.csC Θ ≤ 0.003013635808 + 0.000685847179 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12319 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12319 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12319 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259845829 +
        (6863 / 10000) * 0.000259845829 * 12319 * 0.001039450836) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003013635808 + 0.000685847179 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12319 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12319 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12319 0.011 Θ ∧ gammaRatio 12319 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12319 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12319) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12319 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12319 0.011 Θ) :=
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
    badAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12319 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12319 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12319 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12319 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12319 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12319 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12319 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12319 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12319 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12319 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12319 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004113635808 + 0.003400476218 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12319

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12319
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12319 BstLean.Part154.csC) (piBar (rhoBar 12319 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12319 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12319 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12319 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12319 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12319 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12319 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12319 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12319 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12319 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12319 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12319 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12319 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053298613442 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12319) ≤ 0.010759770450 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12319 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010759770450 + 2 * 0.737676 / 12319) := by gcongr
    _ ≤ (0.053298613442 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12319 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12319

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12319
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485805454 : ℝ) ≤ plow 12319 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12319) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405485823)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425180246) : eMP 12319 0.011 xi bn ≤ 0.001226193435 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12319 : ℝ) * (1 - 0.011))) ≤ 0.000606211240 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001425180246 / (12319 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606211240 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606211240 : ℝ) + 3.141593 * 0.053405485823 / (12319 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001226193435 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405485823)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425180246) : PiBarMP 12319 12 0.011 xi bn ≤ 0.163760397344 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12319 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037751559518 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.378852141159 : ℝ) ≤ √((12319 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.990990625365 : ℝ) ≤ √12319 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12319) ≤ 0.125527380054 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037751559518 + 0.053405485823 * 1.772454 / (2 * (110.378852141159 : ℝ))) * (1 + 0.001226193435) +
        8 / (12319 * 110.990990625365) + 0.125527380054 := by gcongr
    _ ≤ (0.163760397344 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405485823)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425180246) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284394883042) :
    parallelOracle 12319 0.011 xi bn cd ≤ 0.164784793534 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12319 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12319 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485805454 : ℝ) ≤ plow 12319 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.990990625365 : ℝ) ≤ √12319 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284394883042 : ℝ) / (2 * 0.560485805454 * 110.990990625365)) * 0.163760397344 +
        0.284394883042 ^ 2 / (2 * 0.560485805454 * 110.990990625365) := by gcongr
    _ ≤ (0.164784793534 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405485823) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425180246)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284394883042) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12319 12319 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485805454 : ℝ) ≤ plow 12319 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.990990625365 : ℝ) ≤ √12319 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12319 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12319 Θ 1.22 ≤ 0.011947821103 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.990990625365 := by gcongr <;> linarith
      _ ≤ (0.011947821103 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12319 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12319 12319 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12319 12319 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12319 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12319 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12319 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12319 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164784793534 + 0.011947821103 + (0.008646 : ℝ) *
        (1 + 2 * (0.284394883042 + 0.011947821103) / (0.560485805454 * 110.990990625365))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12319]

end BstLean.Part264b.N12319

/-! The original eight local profiles supply actual 12319 moment certificates. -/
namespace BstLean.Part264b.N12319
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12319 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053405485823 ∧
    0 ≤ bN 12319 BstLean.Part154.csC (groupTheta g) ∧ bN 12319 BstLean.Part154.csC (groupTheta g) ≤ 0.001425180246 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12319 12319 0.011
      (momentAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12319 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12319 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12319 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231096269600 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12319 0.011
      (momentAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12319 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12319
/-! The actual computed-centre upper energy formula at 12319. -/
namespace BstLean.Part264b.N12319
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12319

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12319
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12319 cell12319)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086691539984
  | 2 => 0.087658540237
  | 3 => 0.088627556775
  | 4 => 0.089600873001
  | 5 => 0.090581217413
  | 6 => 0.091571825226
  | 7 => 0.092576504979
  | 8 => 0.093599710063
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12319 12319 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12319 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12319

/-! Actual upper energy certificates on all 43 source endpoints at 12319. -/
namespace BstLean.Part264b.N12319
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12319 cell12319)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12319 (gMinus 12319) (1 - (cell12319 i).lower) ≤ 1 ∧
    energyUpper 12319 (gMinus 12319) (BstLean.Part211.gPlus 12319)
      (finiteEnergy 12319 12319 0.011) (1 - (cell12319 i).lower) ≤
      (cell12319 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12319) (by norm_num)
        (q := 1 - (cell12319 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12319,cell12319]) (by norm_num [scalarRow12319,cell12319])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12319,cell12319])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12319

/-! Source-cell containment and simple scalar guards at 12319. -/
namespace BstLean.Part264b.N12319
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12319 cell12319)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12319 ⟨10,by decide⟩).lower ∧ (cell12319 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12319 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12319 ⟨11,by decide⟩).lower ∧ (cell12319 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12319 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12319 ⟨12,by decide⟩).lower ∧ (cell12319 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12319 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12319 ⟨13,by decide⟩).lower ∧ (cell12319 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12319 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12319 ⟨14,by decide⟩).lower ∧ (cell12319 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12319 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12319 ⟨15,by decide⟩).lower ∧ (cell12319 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12319 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12319 ⟨16,by decide⟩).lower ∧ (cell12319 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12319 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12319 ⟨17,by decide⟩).lower ∧ (cell12319 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12319 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12319 ⟨18,by decide⟩).lower ∧ (cell12319 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12319 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12319 ⟨19,by decide⟩).lower ∧ (cell12319 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12319 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12319 ⟨20,by decide⟩).lower ∧ (cell12319 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12319 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12319 ⟨21,by decide⟩).lower ∧ (cell12319 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12319 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12319 ⟨22,by decide⟩).lower ∧ (cell12319 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12319 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12319 ⟨23,by decide⟩).lower ∧ (cell12319 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12319 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12319 ⟨24,by decide⟩).lower ∧ (cell12319 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12319 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12319 ⟨25,by decide⟩).lower ∧ (cell12319 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12319 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12319 ⟨26,by decide⟩).lower ∧ (cell12319 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12319 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12319 ⟨27,by decide⟩).lower ∧ (cell12319 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12319 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12319 ⟨28,by decide⟩).lower ∧ (cell12319 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12319 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12319 ⟨29,by decide⟩).lower ∧ (cell12319 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12319 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12319 ⟨30,by decide⟩).lower ∧ (cell12319 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12319 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12319 ⟨31,by decide⟩).lower ∧ (cell12319 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12319 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12319 ⟨32,by decide⟩).lower ∧ (cell12319 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12319 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12319 ⟨33,by decide⟩).lower ∧ (cell12319 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12319 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12319 ⟨34,by decide⟩).lower ∧ (cell12319 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12319 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12319 ⟨35,by decide⟩).lower ∧ (cell12319 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12319 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12319 ⟨36,by decide⟩).lower ∧ (cell12319 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12319 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12319 ⟨37,by decide⟩).lower ∧ (cell12319 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12319 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12319 ⟨38,by decide⟩).lower ∧ (cell12319 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12319 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12319 ⟨39,by decide⟩).lower ∧ (cell12319 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12319 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12319 ⟨40,by decide⟩).lower ∧ (cell12319 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12319 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12319 ⟨41,by decide⟩).lower ∧ (cell12319 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12319 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12319 ⟨42,by decide⟩).lower ∧ (cell12319 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12319 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12319 ⟨43,by decide⟩).lower ∧ (cell12319 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12319 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12319 ⟨44,by decide⟩).lower ∧ (cell12319 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12319 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12319 ⟨45,by decide⟩).lower ∧ (cell12319 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12319 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12319 ⟨46,by decide⟩).lower ∧ (cell12319 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12319 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12319 ⟨47,by decide⟩).lower ∧ (cell12319 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12319 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12319 ⟨48,by decide⟩).lower ∧ (cell12319 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12319 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12319 ⟨49,by decide⟩).lower ∧ (cell12319 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12319 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12319 ⟨50,by decide⟩).lower ∧ (cell12319 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12319 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12319 ⟨51,by decide⟩).lower ∧ (cell12319 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12319 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12319 ⟨52,by decide⟩).lower ∧ (cell12319 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12319 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12319 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12319 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12319,cell12319,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12319 i).lower ∧
    (cell12319 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12319 i).upper ≤ (0.532 : ℝ) ∧
    (cell12319 i).centre ≤ (0.1 : ℝ) ∧ (cell12319 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12319 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12319 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12319

/-! The local source numeric instances at 12319 have no network premises. -/
namespace BstLean.Part264b.N12319
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12319 cell12319)

noncomputable def sourceNumerics12319 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12319 (cell12319 i)
      scalarRow12319.M scalarRow12319.H scalarRow12319.xi := by
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
    energy_allowance := scalarRow12319.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12319]
    centre_nonneg := (scalarRow12319.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12319]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12319
/-! Actual 12320 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12320
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12320 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12320 12320 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12320.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12320 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12320 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12320 := gPlus_lower 12320
end BstLean.Part264b.N12320

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12320
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036362173832 : ℝ) ≤ wn 12320 := by
  have hn : √(12320 : ℝ) ≤ 110.995495404093 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12320 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.995495404093 ≤ 2 / √12320 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259788532 : ℝ) ≤ rhoBar 12320 BstLean.Part154.csC ∧
    rhoBar 12320 BstLean.Part154.csC ≤ 0.000259824737 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036362173832 : ℝ) / (1.295212 * 12320) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12320) := by gcongr
      _ ≤ (0.000259824737 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12320 BstLean.Part154.csC) ≤ 0.001039366457 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12320 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12320 BstLean.Part154.csC) (piBar (rhoBar 12320 BstLean.Part154.csC)) ≤ 0.000198456178 ∧
    cc1 (rhoBar 12320 BstLean.Part154.csC) (piBar (rhoBar 12320 BstLean.Part154.csC)) ≤ 0.000126278924 ∧
    cc2 (rhoBar 12320 BstLean.Part154.csC) ≤ 0.000073305810 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12320 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12320 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12320 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12320 BstLean.Part154.csC * nuR (rhoBar 12320 BstLean.Part154.csC)) ≤ 0.000519666351 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259824737 : ℝ) * 0.001039366457 := by gcongr
      _ ≤ (0.000519666351 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12320 BstLean.Part154.csC) * nuR (rhoBar 12320 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039366457 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12320 BstLean.Part154.csC) * rhoBar 12320 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259824737 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259824737 / 2 + 0.399 * 0.001039366457 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198456178 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519666351 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126278924 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259824737 / 1.414213562 := by gcongr
      _ ≤ (0.000073305810 : ℝ) := by norm_num

end BstLean.Part264b.N12320

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12320
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12320 BstLean.Part154.csC) (piBar (rhoBar 12320 BstLean.Part154.csC)) ≤ 1.70084E-7 := by
  have hr0 : 0 ≤ rhoBar 12320 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12320 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12320 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12320 BstLean.Part154.csC) (piBar (rhoBar 12320 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12320 BstLean.Part154.csC) (piBar (rhoBar 12320 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12320 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198456178 : ℝ) ^ 2 + 0.000126278924 ^ 2 + 3 * 0.000073305810 ^ 2 +
        2 * 0.797885 * 0.000198456178 * 0.000126278924 + 2 * 0.000198456178 * 0.000073305810 +
        4 * 0.797885 * 0.000126278924 * 0.000073305810 := by gcongr
    _ ≤ (1.70084E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12320 BstLean.Part154.csC Θ ≤ 0.002714406446 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12320 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12320 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12320 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12320 BstLean.Part154.csC) (piBar (rhoBar 12320 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12320 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70084E-7 / (0.000259788532 : ℝ) := by gcongr
    _ ≤ 0.002714406446 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12320 BstLean.Part154.csC Θ ≤ 0.003013391164 + 0.000685791508 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12320 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12320 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12320 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259824737 +
        (6863 / 10000) * 0.000259824737 * 12320 * 0.001039366457) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003013391164 + 0.000685791508 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12320 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12320 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12320 0.011 Θ ∧ gammaRatio 12320 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12320 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12320) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12320 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12320 0.011 Θ) :=
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
    badAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12320 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12320 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12320 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12320 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12320 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12320 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12320 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12320 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12320 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12320 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12320 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004113391164 + 0.003400197954 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12320

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12320
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12320 BstLean.Part154.csC) (piBar (rhoBar 12320 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12320 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12320 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12320 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12320 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12320 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12320 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12320 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12320 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12320 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12320 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12320 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12320 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053296426493 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12320) ≤ 0.010759333762 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12320 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010759333762 + 2 * 0.737676 / 12320) := by gcongr
    _ ≤ (0.053296426493 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12320 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12320

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12320
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485853514 : ℝ) ≤ plow 12320 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12320) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405095090)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425063385) : eMP 12320 0.011 xi bn ≤ 0.001226093303 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12320 : ℝ) * (1 - 0.011))) ≤ 0.000606161783 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001425063385 / (12320 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606161783 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606161783 : ℝ) + 3.141593 * 0.053405095090 / (12320 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001226093303 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405095090)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425063385) : PiBarMP 12320 12 0.011 xi bn ≤ 0.163753727991 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12320 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037750011722 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.383332075091 : ℝ) ≤ √((12320 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.995495404092 : ℝ) ≤ √12320 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12320) ≤ 0.125522285495 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037750011722 + 0.053405095090 * 1.772454 / (2 * (110.383332075091 : ℝ))) * (1 + 0.001226093303) +
        8 / (12320 * 110.995495404092) + 0.125522285495 := by gcongr
    _ ≤ (0.163753727991 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405095090)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425063385) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284391850702) :
    parallelOracle 12320 0.011 xi bn cd ≤ 0.164778049421 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12320 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12320 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485853514 : ℝ) ≤ plow 12320 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.995495404092 : ℝ) ≤ √12320 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284391850702 : ℝ) / (2 * 0.560485853514 * 110.995495404092)) * 0.163753727991 +
        0.284391850702 ^ 2 / (2 * 0.560485853514 * 110.995495404092) := by gcongr
    _ ≤ (0.164778049421 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053405095090) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001425063385)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284391850702) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12320 12320 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485853514 : ℝ) ≤ plow 12320 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.995495404092 : ℝ) ≤ √12320 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12320 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12320 Θ 1.22 ≤ 0.011947336198 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.995495404092 := by gcongr <;> linarith
      _ ≤ (0.011947336198 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12320 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12320 12320 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12320 12320 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12320 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12320 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12320 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12320 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164778049421 + 0.011947336198 + (0.008646 : ℝ) *
        (1 + 2 * (0.284391850702 + 0.011947336198) / (0.560485853514 * 110.995495404092))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12320]

end BstLean.Part264b.N12320

/-! The original eight local profiles supply actual 12320 moment certificates. -/
namespace BstLean.Part264b.N12320
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12320 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053405095090 ∧
    0 ≤ bN 12320 BstLean.Part154.csC (groupTheta g) ∧ bN 12320 BstLean.Part154.csC (groupTheta g) ≤ 0.001425063385 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12320 12320 0.011
      (momentAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12320 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12320 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12320 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231095424209 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12320 0.011
      (momentAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12320 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12320
/-! The actual computed-centre upper energy formula at 12320. -/
namespace BstLean.Part264b.N12320
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12320

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12320
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12320 cell12320)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086688116925
  | 2 => 0.087655041672
  | 3 => 0.088623969765
  | 4 => 0.089597181794
  | 5 => 0.090577402977
  | 6 => 0.091567864728
  | 7 => 0.092572371211
  | 8 => 0.093595370811
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12320 12320 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12320 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12320

/-! Actual upper energy certificates on all 43 source endpoints at 12320. -/
namespace BstLean.Part264b.N12320
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12320 cell12320)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12320 (gMinus 12320) (1 - (cell12320 i).lower) ≤ 1 ∧
    energyUpper 12320 (gMinus 12320) (BstLean.Part211.gPlus 12320)
      (finiteEnergy 12320 12320 0.011) (1 - (cell12320 i).lower) ≤
      (cell12320 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12320) (by norm_num)
        (q := 1 - (cell12320 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12320,cell12320]) (by norm_num [scalarRow12320,cell12320])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12320,cell12320])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12320

/-! Source-cell containment and simple scalar guards at 12320. -/
namespace BstLean.Part264b.N12320
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12320 cell12320)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12320 ⟨10,by decide⟩).lower ∧ (cell12320 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12320 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12320 ⟨11,by decide⟩).lower ∧ (cell12320 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12320 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12320 ⟨12,by decide⟩).lower ∧ (cell12320 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12320 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12320 ⟨13,by decide⟩).lower ∧ (cell12320 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12320 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12320 ⟨14,by decide⟩).lower ∧ (cell12320 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12320 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12320 ⟨15,by decide⟩).lower ∧ (cell12320 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12320 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12320 ⟨16,by decide⟩).lower ∧ (cell12320 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12320 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12320 ⟨17,by decide⟩).lower ∧ (cell12320 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12320 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12320 ⟨18,by decide⟩).lower ∧ (cell12320 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12320 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12320 ⟨19,by decide⟩).lower ∧ (cell12320 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12320 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12320 ⟨20,by decide⟩).lower ∧ (cell12320 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12320 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12320 ⟨21,by decide⟩).lower ∧ (cell12320 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12320 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12320 ⟨22,by decide⟩).lower ∧ (cell12320 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12320 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12320 ⟨23,by decide⟩).lower ∧ (cell12320 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12320 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12320 ⟨24,by decide⟩).lower ∧ (cell12320 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12320 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12320 ⟨25,by decide⟩).lower ∧ (cell12320 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12320 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12320 ⟨26,by decide⟩).lower ∧ (cell12320 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12320 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12320 ⟨27,by decide⟩).lower ∧ (cell12320 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12320 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12320 ⟨28,by decide⟩).lower ∧ (cell12320 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12320 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12320 ⟨29,by decide⟩).lower ∧ (cell12320 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12320 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12320 ⟨30,by decide⟩).lower ∧ (cell12320 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12320 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12320 ⟨31,by decide⟩).lower ∧ (cell12320 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12320 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12320 ⟨32,by decide⟩).lower ∧ (cell12320 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12320 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12320 ⟨33,by decide⟩).lower ∧ (cell12320 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12320 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12320 ⟨34,by decide⟩).lower ∧ (cell12320 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12320 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12320 ⟨35,by decide⟩).lower ∧ (cell12320 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12320 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12320 ⟨36,by decide⟩).lower ∧ (cell12320 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12320 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12320 ⟨37,by decide⟩).lower ∧ (cell12320 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12320 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12320 ⟨38,by decide⟩).lower ∧ (cell12320 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12320 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12320 ⟨39,by decide⟩).lower ∧ (cell12320 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12320 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12320 ⟨40,by decide⟩).lower ∧ (cell12320 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12320 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12320 ⟨41,by decide⟩).lower ∧ (cell12320 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12320 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12320 ⟨42,by decide⟩).lower ∧ (cell12320 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12320 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12320 ⟨43,by decide⟩).lower ∧ (cell12320 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12320 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12320 ⟨44,by decide⟩).lower ∧ (cell12320 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12320 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12320 ⟨45,by decide⟩).lower ∧ (cell12320 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12320 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12320 ⟨46,by decide⟩).lower ∧ (cell12320 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12320 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12320 ⟨47,by decide⟩).lower ∧ (cell12320 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12320 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12320 ⟨48,by decide⟩).lower ∧ (cell12320 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12320 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12320 ⟨49,by decide⟩).lower ∧ (cell12320 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12320 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12320 ⟨50,by decide⟩).lower ∧ (cell12320 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12320 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12320 ⟨51,by decide⟩).lower ∧ (cell12320 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12320 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12320 ⟨52,by decide⟩).lower ∧ (cell12320 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12320 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12320 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12320 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12320,cell12320,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12320 i).lower ∧
    (cell12320 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12320 i).upper ≤ (0.532 : ℝ) ∧
    (cell12320 i).centre ≤ (0.1 : ℝ) ∧ (cell12320 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12320 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12320 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12320

/-! The local source numeric instances at 12320 have no network premises. -/
namespace BstLean.Part264b.N12320
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12320 cell12320)

noncomputable def sourceNumerics12320 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12320 (cell12320 i)
      scalarRow12320.M scalarRow12320.H scalarRow12320.xi := by
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
    energy_allowance := scalarRow12320.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12320]
    centre_nonneg := (scalarRow12320.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12320]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12320
/-! Actual 12321 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12321
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12321 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12321 12321 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12321.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12321 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12321 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12321 := gPlus_lower 12321
end BstLean.Part264b.N12321

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12321
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036360685009 : ℝ) ≤ wn 12321 := by
  have hn : √(12321 : ℝ) ≤ 111.000000000000 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12321 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.000000000000 ≤ 2 / √12321 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259767074 : ℝ) ≤ rhoBar 12321 BstLean.Part154.csC ∧
    rhoBar 12321 BstLean.Part154.csC ≤ 0.000259803649 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036360685009 : ℝ) / (1.295212 * 12321) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12321) := by gcongr
      _ ≤ (0.000259803649 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12321 BstLean.Part154.csC) ≤ 0.001039282094 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12321 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12321 BstLean.Part154.csC) (piBar (rhoBar 12321 BstLean.Part154.csC)) ≤ 0.000198440070 ∧
    cc1 (rhoBar 12321 BstLean.Part154.csC) (piBar (rhoBar 12321 BstLean.Part154.csC)) ≤ 0.000126268675 ∧
    cc2 (rhoBar 12321 BstLean.Part154.csC) ≤ 0.000073299860 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12321 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12321 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12321 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12321 BstLean.Part154.csC * nuR (rhoBar 12321 BstLean.Part154.csC)) ≤ 0.000519624173 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259803649 : ℝ) * 0.001039282094 := by gcongr
      _ ≤ (0.000519624173 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12321 BstLean.Part154.csC) * nuR (rhoBar 12321 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039282094 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12321 BstLean.Part154.csC) * rhoBar 12321 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259803649 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259803649 / 2 + 0.399 * 0.001039282094 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198440070 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519624173 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126268675 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259803649 / 1.414213562 := by gcongr
      _ ≤ (0.000073299860 : ℝ) := by norm_num

end BstLean.Part264b.N12321

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12321
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12321 BstLean.Part154.csC) (piBar (rhoBar 12321 BstLean.Part154.csC)) ≤ 1.70057E-7 := by
  have hr0 : 0 ≤ rhoBar 12321 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12321 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12321 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12321 BstLean.Part154.csC) (piBar (rhoBar 12321 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12321 BstLean.Part154.csC) (piBar (rhoBar 12321 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12321 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198440070 : ℝ) ^ 2 + 0.000126268675 ^ 2 + 3 * 0.000073299860 ^ 2 +
        2 * 0.797885 * 0.000198440070 * 0.000126268675 + 2 * 0.000198440070 * 0.000073299860 +
        4 * 0.797885 * 0.000126268675 * 0.000073299860 := by gcongr
    _ ≤ (1.70057E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12321 BstLean.Part154.csC Θ ≤ 0.002714199734 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12321 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12321 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12321 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12321 BstLean.Part154.csC) (piBar (rhoBar 12321 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12321 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70057E-7 / (0.000259767074 : ℝ) := by gcongr
    _ ≤ 0.002714199734 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12321 BstLean.Part154.csC Θ ≤ 0.003013146574 + 0.000685735847 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12321 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12321 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12321 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259803649 +
        (6863 / 10000) * 0.000259803649 * 12321 * 0.001039282094) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003013146574 + 0.000685735847 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12321 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12321 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12321 0.011 Θ ∧ gammaRatio 12321 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12321 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12321) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12321 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12321 0.011 Θ) :=
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
    badAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12321 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12321 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12321 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12321 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12321 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12321 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12321 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12321 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12321 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12321 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12321 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004113146574 + 0.003399935581 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12321

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12321
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12321 BstLean.Part154.csC) (piBar (rhoBar 12321 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12321 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12321 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12321 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12321 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12321 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12321 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12321 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12321 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12321 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12321 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12321 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12321 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053294239812 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12321) ≤ 0.010758897127 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12321 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010758897127 + 2 * 0.737676 / 12321) := by gcongr
    _ ≤ (0.053294239812 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12321 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12321

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12321
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485901566 : ℝ) ≤ plow 12321 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12321) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053404712755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424954861) : eMP 12321 0.011 xi bn ≤ 0.001225996728 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12321 : ℝ) * (1 - 0.011))) ≤ 0.000606114104 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001424954861 / (12321 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606114104 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606114104 : ℝ) + 3.141593 * 0.053404712755 / (12321 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225996728 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053404712755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424954861) : PiBarMP 12321 12 0.011 xi bn ≤ 0.163747169965 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12321 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037748574291 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.387811827212 : ℝ) ≤ √((12321 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.000000000000 : ℝ) ≤ √12321 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12321) ≤ 0.125517191557 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037748574291 + 0.053404712755 * 1.772454 / (2 * (110.387811827212 : ℝ))) * (1 + 0.001225996728) +
        8 / (12321 * 111.000000000000) + 0.125517191557 := by gcongr
    _ ≤ (0.163747169965 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053404712755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424954861) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284388836796) :
    parallelOracle 12321 0.011 xi bn cd ≤ 0.164771417005 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12321 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12321 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485901566 : ℝ) ≤ plow 12321 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.000000000000 : ℝ) ≤ √12321 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284388836796 : ℝ) / (2 * 0.560485901566 * 111.000000000000)) * 0.163747169965 +
        0.284388836796 ^ 2 / (2 * 0.560485901566 * 111.000000000000) := by gcongr
    _ ≤ (0.164771417005 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053404712755) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424954861)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284388836796) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12321 12321 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485901566 : ℝ) ≤ plow 12321 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.000000000000 : ℝ) ≤ √12321 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12321 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12321 Θ 1.22 ≤ 0.011946851352 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.000000000000 := by gcongr <;> linarith
      _ ≤ (0.011946851352 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12321 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12321 12321 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12321 12321 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12321 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12321 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12321 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12321 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164771417005 + 0.011946851352 + (0.008646 : ℝ) *
        (1 + 2 * (0.284388836796 + 0.011946851352) / (0.560485901566 * 111.000000000000))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12321]

end BstLean.Part264b.N12321

/-! The original eight local profiles supply actual 12321 moment certificates. -/
namespace BstLean.Part264b.N12321
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12321 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053404712755 ∧
    0 ≤ bN 12321 BstLean.Part154.csC (groupTheta g) ∧ bN 12321 BstLean.Part154.csC (groupTheta g) ≤ 0.001424954861 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12321 12321 0.011
      (momentAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12321 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12321 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12321 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231094596984 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12321 0.011
      (momentAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12321 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12321
/-! The actual computed-centre upper energy formula at 12321. -/
namespace BstLean.Part264b.N12321
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12321

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12321
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12321 cell12321)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086684695490
  | 2 => 0.087651544803
  | 3 => 0.088620384542
  | 4 => 0.089593492484
  | 5 => 0.090573590572
  | 6 => 0.091563906423
  | 7 => 0.092568239832
  | 8 => 0.093591034183
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12321 12321 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12321 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12321

/-! Actual upper energy certificates on all 43 source endpoints at 12321. -/
namespace BstLean.Part264b.N12321
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12321 cell12321)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12321 (gMinus 12321) (1 - (cell12321 i).lower) ≤ 1 ∧
    energyUpper 12321 (gMinus 12321) (BstLean.Part211.gPlus 12321)
      (finiteEnergy 12321 12321 0.011) (1 - (cell12321 i).lower) ≤
      (cell12321 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12321) (by norm_num)
        (q := 1 - (cell12321 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12321,cell12321]) (by norm_num [scalarRow12321,cell12321])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12321,cell12321])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12321

/-! Source-cell containment and simple scalar guards at 12321. -/
namespace BstLean.Part264b.N12321
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12321 cell12321)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12321 ⟨10,by decide⟩).lower ∧ (cell12321 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12321 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12321 ⟨11,by decide⟩).lower ∧ (cell12321 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12321 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12321 ⟨12,by decide⟩).lower ∧ (cell12321 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12321 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12321 ⟨13,by decide⟩).lower ∧ (cell12321 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12321 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12321 ⟨14,by decide⟩).lower ∧ (cell12321 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12321 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12321 ⟨15,by decide⟩).lower ∧ (cell12321 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12321 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12321 ⟨16,by decide⟩).lower ∧ (cell12321 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12321 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12321 ⟨17,by decide⟩).lower ∧ (cell12321 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12321 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12321 ⟨18,by decide⟩).lower ∧ (cell12321 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12321 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12321 ⟨19,by decide⟩).lower ∧ (cell12321 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12321 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12321 ⟨20,by decide⟩).lower ∧ (cell12321 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12321 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12321 ⟨21,by decide⟩).lower ∧ (cell12321 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12321 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12321 ⟨22,by decide⟩).lower ∧ (cell12321 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12321 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12321 ⟨23,by decide⟩).lower ∧ (cell12321 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12321 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12321 ⟨24,by decide⟩).lower ∧ (cell12321 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12321 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12321 ⟨25,by decide⟩).lower ∧ (cell12321 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12321 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12321 ⟨26,by decide⟩).lower ∧ (cell12321 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12321 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12321 ⟨27,by decide⟩).lower ∧ (cell12321 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12321 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12321 ⟨28,by decide⟩).lower ∧ (cell12321 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12321 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12321 ⟨29,by decide⟩).lower ∧ (cell12321 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12321 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12321 ⟨30,by decide⟩).lower ∧ (cell12321 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12321 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12321 ⟨31,by decide⟩).lower ∧ (cell12321 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12321 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12321 ⟨32,by decide⟩).lower ∧ (cell12321 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12321 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12321 ⟨33,by decide⟩).lower ∧ (cell12321 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12321 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12321 ⟨34,by decide⟩).lower ∧ (cell12321 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12321 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12321 ⟨35,by decide⟩).lower ∧ (cell12321 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12321 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12321 ⟨36,by decide⟩).lower ∧ (cell12321 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12321 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12321 ⟨37,by decide⟩).lower ∧ (cell12321 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12321 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12321 ⟨38,by decide⟩).lower ∧ (cell12321 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12321 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12321 ⟨39,by decide⟩).lower ∧ (cell12321 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12321 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12321 ⟨40,by decide⟩).lower ∧ (cell12321 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12321 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12321 ⟨41,by decide⟩).lower ∧ (cell12321 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12321 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12321 ⟨42,by decide⟩).lower ∧ (cell12321 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12321 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12321 ⟨43,by decide⟩).lower ∧ (cell12321 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12321 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12321 ⟨44,by decide⟩).lower ∧ (cell12321 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12321 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12321 ⟨45,by decide⟩).lower ∧ (cell12321 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12321 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12321 ⟨46,by decide⟩).lower ∧ (cell12321 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12321 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12321 ⟨47,by decide⟩).lower ∧ (cell12321 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12321 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12321 ⟨48,by decide⟩).lower ∧ (cell12321 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12321 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12321 ⟨49,by decide⟩).lower ∧ (cell12321 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12321 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12321 ⟨50,by decide⟩).lower ∧ (cell12321 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12321 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12321 ⟨51,by decide⟩).lower ∧ (cell12321 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12321 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12321 ⟨52,by decide⟩).lower ∧ (cell12321 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12321 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12321 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12321 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12321,cell12321,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12321 i).lower ∧
    (cell12321 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12321 i).upper ≤ (0.532 : ℝ) ∧
    (cell12321 i).centre ≤ (0.1 : ℝ) ∧ (cell12321 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12321 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12321 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12321

/-! The local source numeric instances at 12321 have no network premises. -/
namespace BstLean.Part264b.N12321
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12321 cell12321)

noncomputable def sourceNumerics12321 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12321 (cell12321 i)
      scalarRow12321.M scalarRow12321.H scalarRow12321.xi := by
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
    energy_allowance := scalarRow12321.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12321]
    centre_nonneg := (scalarRow12321.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12321]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12321
/-! Actual 12322 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12322
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12322 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12322 12322 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12322.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12322 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12322 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12322 := gPlus_lower 12322
end BstLean.Part264b.N12322

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12322
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036359196368 : ℝ) ≤ wn 12322 := by
  have hn : √(12322 : ℝ) ≤ 111.004504413110 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12322 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.004504413110 ≤ 2 / √12322 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259745620 : ℝ) ≤ rhoBar 12322 BstLean.Part154.csC ∧
    rhoBar 12322 BstLean.Part154.csC ≤ 0.000259782565 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036359196368 : ℝ) / (1.295212 * 12322) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12322) := by gcongr
      _ ≤ (0.000259782565 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12322 BstLean.Part154.csC) ≤ 0.001039197747 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12322 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12322 BstLean.Part154.csC) (piBar (rhoBar 12322 BstLean.Part154.csC)) ≤ 0.000198423965 ∧
    cc1 (rhoBar 12322 BstLean.Part154.csC) (piBar (rhoBar 12322 BstLean.Part154.csC)) ≤ 0.000126258427 ∧
    cc2 (rhoBar 12322 BstLean.Part154.csC) ≤ 0.000073293912 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12322 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12322 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12322 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12322 BstLean.Part154.csC * nuR (rhoBar 12322 BstLean.Part154.csC)) ≤ 0.000519582002 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259782565 : ℝ) * 0.001039197747 := by gcongr
      _ ≤ (0.000519582002 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12322 BstLean.Part154.csC) * nuR (rhoBar 12322 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039197747 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12322 BstLean.Part154.csC) * rhoBar 12322 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259782565 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259782565 / 2 + 0.399 * 0.001039197747 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198423965 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519582002 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126258427 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259782565 / 1.414213562 := by gcongr
      _ ≤ (0.000073293912 : ℝ) := by norm_num

end BstLean.Part264b.N12322

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12322
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12322 BstLean.Part154.csC) (piBar (rhoBar 12322 BstLean.Part154.csC)) ≤ 1.70029E-7 := by
  have hr0 : 0 ≤ rhoBar 12322 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12322 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12322 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12322 BstLean.Part154.csC) (piBar (rhoBar 12322 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12322 BstLean.Part154.csC) (piBar (rhoBar 12322 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12322 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198423965 : ℝ) ^ 2 + 0.000126258427 ^ 2 + 3 * 0.000073293912 ^ 2 +
        2 * 0.797885 * 0.000198423965 * 0.000126258427 + 2 * 0.000198423965 * 0.000073293912 +
        4 * 0.797885 * 0.000126258427 * 0.000073293912 := by gcongr
    _ ≤ (1.70029E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12322 BstLean.Part154.csC Θ ≤ 0.002713976985 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12322 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12322 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12322 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12322 BstLean.Part154.csC) (piBar (rhoBar 12322 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12322 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70029E-7 / (0.000259745620 : ℝ) := by gcongr
    _ ≤ 0.002713976985 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12322 BstLean.Part154.csC Θ ≤ 0.003012902036 + 0.000685680197 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12322 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12322 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12322 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259782565 +
        (6863 / 10000) * 0.000259782565 * 12322 * 0.001039197747) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003012902036 + 0.000685680197 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12322 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12322 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12322 0.011 Θ ∧ gammaRatio 12322 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12322 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12322) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12322 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12322 0.011 Θ) :=
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
    badAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12322 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12322 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12322 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12322 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12322 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12322 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12322 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12322 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12322 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12322 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12322 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004112902036 + 0.003399657182 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12322

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12322
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12322 BstLean.Part154.csC) (piBar (rhoBar 12322 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12322 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12322 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12322 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12322 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12322 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12322 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12322 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12322 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12322 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12322 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12322 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12322 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053292053403 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12322) ≤ 0.010758460546 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12322 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010758460546 + 2 * 0.737676 / 12322) := by gcongr
    _ ≤ (0.053292053403 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12322 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12322

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12322
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485949610 : ℝ) ≤ plow 12322 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12322) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053404322057)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424837918) : eMP 12322 0.011 xi bn ≤ 0.001225896578 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12322 : ℝ) * (1 - 0.011))) ≤ 0.000606064638 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001424837918 / (12322 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606064638 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606064638 : ℝ) + 3.141593 * 0.053404322057 / (12322 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225896578 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053404322057)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424837918) : PiBarMP 12322 12 0.011 xi bn ≤ 0.163740500648 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12322 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037747025287 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.392291397542 : ℝ) ≤ √((12322 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.004504413109 : ℝ) ≤ √12322 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12322) ≤ 0.125512098238 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037747025287 + 0.053404322057 * 1.772454 / (2 * (110.392291397542 : ℝ))) * (1 + 0.001225896578) +
        8 / (12322 * 111.004504413109) + 0.125512098238 := by gcongr
    _ ≤ (0.163740500648 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053404322057)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424837918) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284385805065) :
    parallelOracle 12322 0.011 xi bn cd ≤ 0.164764672948 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12322 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12322 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485949610 : ℝ) ≤ plow 12322 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.004504413109 : ℝ) ≤ √12322 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284385805065 : ℝ) / (2 * 0.560485949610 * 111.004504413109)) * 0.163740500648 +
        0.284385805065 ^ 2 / (2 * 0.560485949610 * 111.004504413109) := by gcongr
    _ ≤ (0.164764672948 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053404322057) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424837918)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284385805065) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12322 12322 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485949610 : ℝ) ≤ plow 12322 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.004504413109 : ℝ) ≤ √12322 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12322 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12322 Θ 1.22 ≤ 0.011946366565 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.004504413109 := by gcongr <;> linarith
      _ ≤ (0.011946366565 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12322 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12322 12322 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12322 12322 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12322 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12322 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12322 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12322 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164764672948 + 0.011946366565 + (0.008646 : ℝ) *
        (1 + 2 * (0.284385805065 + 0.011946366565) / (0.560485949610 * 111.004504413109))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12322]

end BstLean.Part264b.N12322

/-! The original eight local profiles supply actual 12322 moment certificates. -/
namespace BstLean.Part264b.N12322
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12322 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053404322057 ∧
    0 ≤ bN 12322 BstLean.Part154.csC (groupTheta g) ∧ bN 12322 BstLean.Part154.csC (groupTheta g) ≤ 0.001424837918 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12322 12322 0.011
      (momentAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12322 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12322 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12322 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231093751662 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12322 0.011
      (momentAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12322 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12322
/-! The actual computed-centre upper energy formula at 12322. -/
namespace BstLean.Part264b.N12322
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12322

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12322
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12322 cell12322)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086681275676
  | 2 => 0.087648049629
  | 3 => 0.088616801103
  | 4 => 0.089589805068
  | 5 => 0.090569780196
  | 6 => 0.091559950310
  | 7 => 0.092564110840
  | 8 => 0.093586700175
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12322 12322 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12322 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12322

/-! Actual upper energy certificates on all 43 source endpoints at 12322. -/
namespace BstLean.Part264b.N12322
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12322 cell12322)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12322 (gMinus 12322) (1 - (cell12322 i).lower) ≤ 1 ∧
    energyUpper 12322 (gMinus 12322) (BstLean.Part211.gPlus 12322)
      (finiteEnergy 12322 12322 0.011) (1 - (cell12322 i).lower) ≤
      (cell12322 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12322) (by norm_num)
        (q := 1 - (cell12322 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12322,cell12322]) (by norm_num [scalarRow12322,cell12322])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12322,cell12322])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12322

/-! Source-cell containment and simple scalar guards at 12322. -/
namespace BstLean.Part264b.N12322
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12322 cell12322)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12322 ⟨10,by decide⟩).lower ∧ (cell12322 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12322 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12322 ⟨11,by decide⟩).lower ∧ (cell12322 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12322 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12322 ⟨12,by decide⟩).lower ∧ (cell12322 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12322 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12322 ⟨13,by decide⟩).lower ∧ (cell12322 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12322 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12322 ⟨14,by decide⟩).lower ∧ (cell12322 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12322 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12322 ⟨15,by decide⟩).lower ∧ (cell12322 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12322 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12322 ⟨16,by decide⟩).lower ∧ (cell12322 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12322 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12322 ⟨17,by decide⟩).lower ∧ (cell12322 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12322 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12322 ⟨18,by decide⟩).lower ∧ (cell12322 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12322 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12322 ⟨19,by decide⟩).lower ∧ (cell12322 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12322 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12322 ⟨20,by decide⟩).lower ∧ (cell12322 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12322 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12322 ⟨21,by decide⟩).lower ∧ (cell12322 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12322 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12322 ⟨22,by decide⟩).lower ∧ (cell12322 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12322 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12322 ⟨23,by decide⟩).lower ∧ (cell12322 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12322 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12322 ⟨24,by decide⟩).lower ∧ (cell12322 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12322 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12322 ⟨25,by decide⟩).lower ∧ (cell12322 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12322 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12322 ⟨26,by decide⟩).lower ∧ (cell12322 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12322 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12322 ⟨27,by decide⟩).lower ∧ (cell12322 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12322 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12322 ⟨28,by decide⟩).lower ∧ (cell12322 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12322 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12322 ⟨29,by decide⟩).lower ∧ (cell12322 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12322 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12322 ⟨30,by decide⟩).lower ∧ (cell12322 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12322 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12322 ⟨31,by decide⟩).lower ∧ (cell12322 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12322 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12322 ⟨32,by decide⟩).lower ∧ (cell12322 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12322 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12322 ⟨33,by decide⟩).lower ∧ (cell12322 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12322 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12322 ⟨34,by decide⟩).lower ∧ (cell12322 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12322 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12322 ⟨35,by decide⟩).lower ∧ (cell12322 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12322 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12322 ⟨36,by decide⟩).lower ∧ (cell12322 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12322 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12322 ⟨37,by decide⟩).lower ∧ (cell12322 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12322 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12322 ⟨38,by decide⟩).lower ∧ (cell12322 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12322 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12322 ⟨39,by decide⟩).lower ∧ (cell12322 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12322 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12322 ⟨40,by decide⟩).lower ∧ (cell12322 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12322 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12322 ⟨41,by decide⟩).lower ∧ (cell12322 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12322 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12322 ⟨42,by decide⟩).lower ∧ (cell12322 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12322 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12322 ⟨43,by decide⟩).lower ∧ (cell12322 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12322 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12322 ⟨44,by decide⟩).lower ∧ (cell12322 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12322 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12322 ⟨45,by decide⟩).lower ∧ (cell12322 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12322 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12322 ⟨46,by decide⟩).lower ∧ (cell12322 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12322 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12322 ⟨47,by decide⟩).lower ∧ (cell12322 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12322 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12322 ⟨48,by decide⟩).lower ∧ (cell12322 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12322 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12322 ⟨49,by decide⟩).lower ∧ (cell12322 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12322 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12322 ⟨50,by decide⟩).lower ∧ (cell12322 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12322 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12322 ⟨51,by decide⟩).lower ∧ (cell12322 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12322 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12322 ⟨52,by decide⟩).lower ∧ (cell12322 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12322 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12322 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12322 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12322,cell12322,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12322 i).lower ∧
    (cell12322 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12322 i).upper ≤ (0.532 : ℝ) ∧
    (cell12322 i).centre ≤ (0.1 : ℝ) ∧ (cell12322 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12322 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12322 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12322

/-! The local source numeric instances at 12322 have no network premises. -/
namespace BstLean.Part264b.N12322
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12322 cell12322)

noncomputable def sourceNumerics12322 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12322 (cell12322 i)
      scalarRow12322.M scalarRow12322.H scalarRow12322.xi := by
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
    energy_allowance := scalarRow12322.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12322]
    centre_nonneg := (scalarRow12322.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12322]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12322
/-! Actual 12323 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12323
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12323 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12323 12323 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12323.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12323 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12323 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12323 := gPlus_lower 12323
end BstLean.Part264b.N12323

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12323
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036357707909 : ℝ) ≤ wn 12323 := by
  have hn : √(12323 : ℝ) ≤ 111.009008643443 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12323 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.009008643443 ≤ 2 / √12323 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259724168 : ℝ) ≤ rhoBar 12323 BstLean.Part154.csC ∧
    rhoBar 12323 BstLean.Part154.csC ≤ 0.000259761484 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036357707909 : ℝ) / (1.295212 * 12323) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12323) := by gcongr
      _ ≤ (0.000259761484 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12323 BstLean.Part154.csC) ≤ 0.001039113413 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12323 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12323 BstLean.Part154.csC) (piBar (rhoBar 12323 BstLean.Part154.csC)) ≤ 0.000198407863 ∧
    cc1 (rhoBar 12323 BstLean.Part154.csC) (piBar (rhoBar 12323 BstLean.Part154.csC)) ≤ 0.000126248181 ∧
    cc2 (rhoBar 12323 BstLean.Part154.csC) ≤ 0.000073287964 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12323 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12323 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12323 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12323 BstLean.Part154.csC * nuR (rhoBar 12323 BstLean.Part154.csC)) ≤ 0.000519539837 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259761484 : ℝ) * 0.001039113413 := by gcongr
      _ ≤ (0.000519539837 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12323 BstLean.Part154.csC) * nuR (rhoBar 12323 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039113413 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12323 BstLean.Part154.csC) * rhoBar 12323 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259761484 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259761484 / 2 + 0.399 * 0.001039113413 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198407863 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519539837 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126248181 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259761484 / 1.414213562 := by gcongr
      _ ≤ (0.000073287964 : ℝ) := by norm_num

end BstLean.Part264b.N12323

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12323
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12323 BstLean.Part154.csC) (piBar (rhoBar 12323 BstLean.Part154.csC)) ≤ 1.70001E-7 := by
  have hr0 : 0 ≤ rhoBar 12323 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12323 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12323 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12323 BstLean.Part154.csC) (piBar (rhoBar 12323 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12323 BstLean.Part154.csC) (piBar (rhoBar 12323 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12323 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198407863 : ℝ) ^ 2 + 0.000126248181 ^ 2 + 3 * 0.000073287964 ^ 2 +
        2 * 0.797885 * 0.000198407863 * 0.000126248181 + 2 * 0.000198407863 * 0.000073287964 +
        4 * 0.797885 * 0.000126248181 * 0.000073287964 := by gcongr
    _ ≤ (1.70001E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12323 BstLean.Part154.csC Θ ≤ 0.002713754178 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12323 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12323 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12323 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12323 BstLean.Part154.csC) (piBar (rhoBar 12323 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12323 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70001E-7 / (0.000259724168 : ℝ) := by gcongr
    _ ≤ 0.002713754178 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12323 BstLean.Part154.csC Θ ≤ 0.003012657531 + 0.000685624555 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12323 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12323 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12323 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259761484 +
        (6863 / 10000) * 0.000259761484 * 12323 * 0.001039113413) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003012657531 + 0.000685624555 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12323 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12323 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12323 0.011 Θ ∧ gammaRatio 12323 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12323 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12323) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12323 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12323 0.011 Θ) :=
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
    badAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12323 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12323 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12323 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12323 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12323 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12323 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12323 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12323 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12323 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12323 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12323 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004112657531 + 0.003399378733 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12323

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12323
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12323 BstLean.Part154.csC) (piBar (rhoBar 12323 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12323 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12323 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12323 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12323 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12323 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12323 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12323 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12323 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12323 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12323 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12323 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12323 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053289867257 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12323) ≤ 0.010758024017 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12323 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010758024017 + 2 * 0.737676 / 12323) := by gcongr
    _ ≤ (0.053289867257 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12323 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12323

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12323
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560485997646 : ℝ) ≤ plow 12323 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12323) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403931366)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424720944) : eMP 12323 0.011 xi bn ≤ 0.001225796422 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12323 : ℝ) * (1 - 0.011))) ≤ 0.000606015169 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001424720944 / (12323 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000606015169 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000606015169 : ℝ) + 3.141593 * 0.053403931366 / (12323 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225796422 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403931366)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424720944) : PiBarMP 12323 12 0.011 xi bn ≤ 0.163733831480 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12323 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037745475809 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.396770786105 : ℝ) ≤ √((12323 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.009008643442 : ℝ) ≤ √12323 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12323) ≤ 0.125507005540 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037745475809 + 0.053403931366 * 1.772454 / (2 * (110.396770786105 : ℝ))) * (1 + 0.001225796422) +
        8 / (12323 * 111.009008643442) + 0.125507005540 := by gcongr
    _ ≤ (0.163733831480 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403931366)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424720944) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284382773609) :
    parallelOracle 12323 0.011 xi bn cd ≤ 0.164757929050 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12323 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12323 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560485997646 : ℝ) ≤ plow 12323 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.009008643442 : ℝ) ≤ √12323 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284382773609 : ℝ) / (2 * 0.560485997646 * 111.009008643442)) * 0.163733831480 +
        0.284382773609 ^ 2 / (2 * 0.560485997646 * 111.009008643442) := by gcongr
    _ ≤ (0.164757929050 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403931366) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424720944)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284382773609) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12323 12323 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560485997646 : ℝ) ≤ plow 12323 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.009008643442 : ℝ) ≤ √12323 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12323 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12323 Θ 1.22 ≤ 0.011945881837 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.009008643442 := by gcongr <;> linarith
      _ ≤ (0.011945881837 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12323 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12323 12323 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12323 12323 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12323 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12323 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12323 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12323 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164757929050 + 0.011945881837 + (0.008646 : ℝ) *
        (1 + 2 * (0.284382773609 + 0.011945881837) / (0.560485997646 * 111.009008643442))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12323]

end BstLean.Part264b.N12323

/-! The original eight local profiles supply actual 12323 moment certificates. -/
namespace BstLean.Part264b.N12323
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12323 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053403931366 ∧
    0 ≤ bN 12323 BstLean.Part154.csC (groupTheta g) ∧ bN 12323 BstLean.Part154.csC (groupTheta g) ≤ 0.001424720944 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12323 12323 0.011
      (momentAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12323 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12323 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12323 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231092906352 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12323 0.011
      (momentAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12323 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12323
/-! The actual computed-centre upper energy formula at 12323. -/
namespace BstLean.Part264b.N12323
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12323

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12323
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12323 cell12323)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086677857482
  | 2 => 0.087644556148
  | 3 => 0.088613219446
  | 4 => 0.089586119546
  | 5 => 0.090565971847
  | 6 => 0.091555996386
  | 7 => 0.092559984232
  | 8 => 0.093582368785
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12323 12323 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12323 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12323

/-! Actual upper energy certificates on all 43 source endpoints at 12323. -/
namespace BstLean.Part264b.N12323
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12323 cell12323)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12323 (gMinus 12323) (1 - (cell12323 i).lower) ≤ 1 ∧
    energyUpper 12323 (gMinus 12323) (BstLean.Part211.gPlus 12323)
      (finiteEnergy 12323 12323 0.011) (1 - (cell12323 i).lower) ≤
      (cell12323 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12323) (by norm_num)
        (q := 1 - (cell12323 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12323,cell12323]) (by norm_num [scalarRow12323,cell12323])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12323,cell12323])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12323

/-! Source-cell containment and simple scalar guards at 12323. -/
namespace BstLean.Part264b.N12323
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12323 cell12323)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12323 ⟨10,by decide⟩).lower ∧ (cell12323 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12323 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12323 ⟨11,by decide⟩).lower ∧ (cell12323 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12323 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12323 ⟨12,by decide⟩).lower ∧ (cell12323 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12323 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12323 ⟨13,by decide⟩).lower ∧ (cell12323 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12323 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12323 ⟨14,by decide⟩).lower ∧ (cell12323 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12323 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12323 ⟨15,by decide⟩).lower ∧ (cell12323 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12323 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12323 ⟨16,by decide⟩).lower ∧ (cell12323 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12323 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12323 ⟨17,by decide⟩).lower ∧ (cell12323 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12323 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12323 ⟨18,by decide⟩).lower ∧ (cell12323 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12323 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12323 ⟨19,by decide⟩).lower ∧ (cell12323 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12323 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12323 ⟨20,by decide⟩).lower ∧ (cell12323 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12323 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12323 ⟨21,by decide⟩).lower ∧ (cell12323 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12323 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12323 ⟨22,by decide⟩).lower ∧ (cell12323 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12323 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12323 ⟨23,by decide⟩).lower ∧ (cell12323 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12323 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12323 ⟨24,by decide⟩).lower ∧ (cell12323 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12323 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12323 ⟨25,by decide⟩).lower ∧ (cell12323 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12323 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12323 ⟨26,by decide⟩).lower ∧ (cell12323 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12323 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12323 ⟨27,by decide⟩).lower ∧ (cell12323 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12323 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12323 ⟨28,by decide⟩).lower ∧ (cell12323 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12323 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12323 ⟨29,by decide⟩).lower ∧ (cell12323 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12323 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12323 ⟨30,by decide⟩).lower ∧ (cell12323 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12323 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12323 ⟨31,by decide⟩).lower ∧ (cell12323 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12323 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12323 ⟨32,by decide⟩).lower ∧ (cell12323 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12323 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12323 ⟨33,by decide⟩).lower ∧ (cell12323 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12323 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12323 ⟨34,by decide⟩).lower ∧ (cell12323 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12323 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12323 ⟨35,by decide⟩).lower ∧ (cell12323 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12323 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12323 ⟨36,by decide⟩).lower ∧ (cell12323 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12323 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12323 ⟨37,by decide⟩).lower ∧ (cell12323 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12323 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12323 ⟨38,by decide⟩).lower ∧ (cell12323 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12323 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12323 ⟨39,by decide⟩).lower ∧ (cell12323 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12323 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12323 ⟨40,by decide⟩).lower ∧ (cell12323 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12323 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12323 ⟨41,by decide⟩).lower ∧ (cell12323 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12323 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12323 ⟨42,by decide⟩).lower ∧ (cell12323 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12323 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12323 ⟨43,by decide⟩).lower ∧ (cell12323 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12323 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12323 ⟨44,by decide⟩).lower ∧ (cell12323 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12323 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12323 ⟨45,by decide⟩).lower ∧ (cell12323 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12323 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12323 ⟨46,by decide⟩).lower ∧ (cell12323 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12323 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12323 ⟨47,by decide⟩).lower ∧ (cell12323 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12323 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12323 ⟨48,by decide⟩).lower ∧ (cell12323 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12323 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12323 ⟨49,by decide⟩).lower ∧ (cell12323 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12323 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12323 ⟨50,by decide⟩).lower ∧ (cell12323 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12323 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12323 ⟨51,by decide⟩).lower ∧ (cell12323 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12323 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12323 ⟨52,by decide⟩).lower ∧ (cell12323 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12323 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12323 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12323 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12323,cell12323,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12323 i).lower ∧
    (cell12323 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12323 i).upper ≤ (0.532 : ℝ) ∧
    (cell12323 i).centre ≤ (0.1 : ℝ) ∧ (cell12323 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12323 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12323 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12323

/-! The local source numeric instances at 12323 have no network premises. -/
namespace BstLean.Part264b.N12323
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12323 cell12323)

noncomputable def sourceNumerics12323 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12323 (cell12323 i)
      scalarRow12323.M scalarRow12323.H scalarRow12323.xi := by
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
    energy_allowance := scalarRow12323.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12323]
    centre_nonneg := (scalarRow12323.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12323]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12323
/-! Actual 12324 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12324
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12324 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12324 12324 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12324.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12324 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12324 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12324 := gPlus_lower 12324
end BstLean.Part264b.N12324

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12324
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036356219633 : ℝ) ≤ wn 12324 := by
  have hn : √(12324 : ℝ) ≤ 111.013512691024 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12324 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.013512691024 ≤ 2 / √12324 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259702721 : ℝ) ≤ rhoBar 12324 BstLean.Part154.csC ∧
    rhoBar 12324 BstLean.Part154.csC ≤ 0.000259740406 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036356219633 : ℝ) / (1.295212 * 12324) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12324) := by gcongr
      _ ≤ (0.000259740406 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12324 BstLean.Part154.csC) ≤ 0.001039029090 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12324 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12324 BstLean.Part154.csC) (piBar (rhoBar 12324 BstLean.Part154.csC)) ≤ 0.000198391762 ∧
    cc1 (rhoBar 12324 BstLean.Part154.csC) (piBar (rhoBar 12324 BstLean.Part154.csC)) ≤ 0.000126237936 ∧
    cc2 (rhoBar 12324 BstLean.Part154.csC) ≤ 0.000073282017 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12324 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12324 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12324 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12324 BstLean.Part154.csC * nuR (rhoBar 12324 BstLean.Part154.csC)) ≤ 0.000519497679 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259740406 : ℝ) * 0.001039029090 := by gcongr
      _ ≤ (0.000519497679 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12324 BstLean.Part154.csC) * nuR (rhoBar 12324 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001039029090 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12324 BstLean.Part154.csC) * rhoBar 12324 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259740406 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259740406 / 2 + 0.399 * 0.001039029090 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198391762 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519497679 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126237936 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259740406 / 1.414213562 := by gcongr
      _ ≤ (0.000073282017 : ℝ) := by norm_num

end BstLean.Part264b.N12324

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12324
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12324 BstLean.Part154.csC) (piBar (rhoBar 12324 BstLean.Part154.csC)) ≤ 1.69974E-7 := by
  have hr0 : 0 ≤ rhoBar 12324 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12324 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12324 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12324 BstLean.Part154.csC) (piBar (rhoBar 12324 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12324 BstLean.Part154.csC) (piBar (rhoBar 12324 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12324 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198391762 : ℝ) ^ 2 + 0.000126237936 ^ 2 + 3 * 0.000073282017 ^ 2 +
        2 * 0.797885 * 0.000198391762 * 0.000126237936 + 2 * 0.000198391762 * 0.000073282017 +
        4 * 0.797885 * 0.000126237936 * 0.000073282017 := by gcongr
    _ ≤ (1.69974E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12324 BstLean.Part154.csC Θ ≤ 0.002713547247 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12324 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12324 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12324 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12324 BstLean.Part154.csC) (piBar (rhoBar 12324 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12324 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69974E-7 / (0.000259702721 : ℝ) := by gcongr
    _ ≤ 0.002713547247 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12324 BstLean.Part154.csC Θ ≤ 0.003012413054 + 0.000685568921 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12324 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12324 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12324 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259740406 +
        (6863 / 10000) * 0.000259740406 * 12324 * 0.001039029090) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003012413054 + 0.000685568921 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12324 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12324 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12324 0.011 Θ ∧ gammaRatio 12324 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12324 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12324) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12324 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12324 0.011 Θ) :=
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
    badAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12324 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12324 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12324 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12324 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12324 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12324 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12324 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12324 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12324 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12324 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12324 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004112413054 + 0.003399116168 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12324

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12324
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12324 BstLean.Part154.csC) (piBar (rhoBar 12324 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12324 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12324 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12324 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12324 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12324 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12324 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12324 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12324 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12324 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12324 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12324 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12324 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053287681383 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12324) ≤ 0.010757587542 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12324 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010757587542 + 2 * 0.737676 / 12324) := by gcongr
    _ ≤ (0.053287681383 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12324 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12324

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12324
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486045675 : ℝ) ≤ plow 12324 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12324) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403549043)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424612305) : eMP 12324 0.011 xi bn ≤ 0.001225699823 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12324 : ℝ) * (1 - 0.011))) ≤ 0.000605967477 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001424612305 / (12324 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605967477 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605967477 : ℝ) + 3.141593 * 0.053403549043 / (12324 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225699823 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403549043)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424612305) : PiBarMP 12324 12 0.011 xi bn ≤ 0.163727273624 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12324 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037744036682 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.401249992923 : ℝ) ≤ √((12324 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.013512691023 : ℝ) ≤ √12324 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12324) ≤ 0.125501913462 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037744036682 + 0.053403549043 * 1.772454 / (2 * (110.401249992923 : ℝ))) * (1 + 0.001225699823) +
        8 / (12324 * 111.013512691023) + 0.125501913462 := by gcongr
    _ ≤ (0.163727273624 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403549043)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424612305) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284379760527) :
    parallelOracle 12324 0.011 xi bn cd ≤ 0.164751296835 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12324 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12324 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486045675 : ℝ) ≤ plow 12324 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.013512691023 : ℝ) ≤ √12324 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284379760527 : ℝ) / (2 * 0.560486045675 * 111.013512691023)) * 0.163727273624 +
        0.284379760527 ^ 2 / (2 * 0.560486045675 * 111.013512691023) := by gcongr
    _ ≤ (0.164751296835 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403549043) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424612305)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284379760527) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12324 12324 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486045675 : ℝ) ≤ plow 12324 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.013512691023 : ℝ) ≤ √12324 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12324 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12324 Θ 1.22 ≤ 0.011945397168 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.013512691023 := by gcongr <;> linarith
      _ ≤ (0.011945397168 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12324 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12324 12324 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12324 12324 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12324 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12324 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12324 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12324 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164751296835 + 0.011945397168 + (0.008646 : ℝ) *
        (1 + 2 * (0.284379760527 + 0.011945397168) / (0.560486045675 * 111.013512691023))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12324]

end BstLean.Part264b.N12324

/-! The original eight local profiles supply actual 12324 moment certificates. -/
namespace BstLean.Part264b.N12324
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12324 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053403549043 ∧
    0 ≤ bN 12324 BstLean.Part154.csC (groupTheta g) ∧ bN 12324 BstLean.Part154.csC (groupTheta g) ≤ 0.001424612305 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12324 12324 0.011
      (momentAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12324 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12324 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12324 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231092079144 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12324 0.011
      (momentAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12324 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12324
/-! The actual computed-centre upper energy formula at 12324. -/
namespace BstLean.Part264b.N12324
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12324

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12324
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12324 cell12324)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086674440906
  | 2 => 0.087641064357
  | 3 => 0.088609639570
  | 4 => 0.089582435913
  | 5 => 0.090562165522
  | 6 => 0.091552044648
  | 7 => 0.092555860006
  | 8 => 0.093578040008
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12324 12324 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12324 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12324

/-! Actual upper energy certificates on all 43 source endpoints at 12324. -/
namespace BstLean.Part264b.N12324
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12324 cell12324)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12324 (gMinus 12324) (1 - (cell12324 i).lower) ≤ 1 ∧
    energyUpper 12324 (gMinus 12324) (BstLean.Part211.gPlus 12324)
      (finiteEnergy 12324 12324 0.011) (1 - (cell12324 i).lower) ≤
      (cell12324 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12324) (by norm_num)
        (q := 1 - (cell12324 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12324,cell12324]) (by norm_num [scalarRow12324,cell12324])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12324,cell12324])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12324

/-! Source-cell containment and simple scalar guards at 12324. -/
namespace BstLean.Part264b.N12324
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12324 cell12324)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12324 ⟨10,by decide⟩).lower ∧ (cell12324 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12324 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12324 ⟨11,by decide⟩).lower ∧ (cell12324 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12324 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12324 ⟨12,by decide⟩).lower ∧ (cell12324 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12324 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12324 ⟨13,by decide⟩).lower ∧ (cell12324 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12324 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12324 ⟨14,by decide⟩).lower ∧ (cell12324 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12324 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12324 ⟨15,by decide⟩).lower ∧ (cell12324 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12324 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12324 ⟨16,by decide⟩).lower ∧ (cell12324 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12324 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12324 ⟨17,by decide⟩).lower ∧ (cell12324 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12324 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12324 ⟨18,by decide⟩).lower ∧ (cell12324 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12324 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12324 ⟨19,by decide⟩).lower ∧ (cell12324 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12324 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12324 ⟨20,by decide⟩).lower ∧ (cell12324 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12324 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12324 ⟨21,by decide⟩).lower ∧ (cell12324 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12324 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12324 ⟨22,by decide⟩).lower ∧ (cell12324 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12324 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12324 ⟨23,by decide⟩).lower ∧ (cell12324 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12324 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12324 ⟨24,by decide⟩).lower ∧ (cell12324 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12324 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12324 ⟨25,by decide⟩).lower ∧ (cell12324 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12324 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12324 ⟨26,by decide⟩).lower ∧ (cell12324 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12324 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12324 ⟨27,by decide⟩).lower ∧ (cell12324 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12324 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12324 ⟨28,by decide⟩).lower ∧ (cell12324 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12324 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12324 ⟨29,by decide⟩).lower ∧ (cell12324 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12324 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12324 ⟨30,by decide⟩).lower ∧ (cell12324 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12324 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12324 ⟨31,by decide⟩).lower ∧ (cell12324 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12324 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12324 ⟨32,by decide⟩).lower ∧ (cell12324 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12324 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12324 ⟨33,by decide⟩).lower ∧ (cell12324 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12324 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12324 ⟨34,by decide⟩).lower ∧ (cell12324 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12324 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12324 ⟨35,by decide⟩).lower ∧ (cell12324 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12324 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12324 ⟨36,by decide⟩).lower ∧ (cell12324 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12324 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12324 ⟨37,by decide⟩).lower ∧ (cell12324 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12324 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12324 ⟨38,by decide⟩).lower ∧ (cell12324 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12324 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12324 ⟨39,by decide⟩).lower ∧ (cell12324 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12324 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12324 ⟨40,by decide⟩).lower ∧ (cell12324 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12324 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12324 ⟨41,by decide⟩).lower ∧ (cell12324 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12324 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12324 ⟨42,by decide⟩).lower ∧ (cell12324 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12324 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12324 ⟨43,by decide⟩).lower ∧ (cell12324 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12324 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12324 ⟨44,by decide⟩).lower ∧ (cell12324 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12324 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12324 ⟨45,by decide⟩).lower ∧ (cell12324 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12324 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12324 ⟨46,by decide⟩).lower ∧ (cell12324 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12324 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12324 ⟨47,by decide⟩).lower ∧ (cell12324 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12324 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12324 ⟨48,by decide⟩).lower ∧ (cell12324 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12324 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12324 ⟨49,by decide⟩).lower ∧ (cell12324 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12324 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12324 ⟨50,by decide⟩).lower ∧ (cell12324 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12324 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12324 ⟨51,by decide⟩).lower ∧ (cell12324 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12324 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12324 ⟨52,by decide⟩).lower ∧ (cell12324 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12324 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12324 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12324 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12324,cell12324,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12324 i).lower ∧
    (cell12324 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12324 i).upper ≤ (0.532 : ℝ) ∧
    (cell12324 i).centre ≤ (0.1 : ℝ) ∧ (cell12324 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12324 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12324 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12324

/-! The local source numeric instances at 12324 have no network premises. -/
namespace BstLean.Part264b.N12324
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12324 cell12324)

noncomputable def sourceNumerics12324 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12324 (cell12324 i)
      scalarRow12324.M scalarRow12324.H scalarRow12324.xi := by
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
    energy_allowance := scalarRow12324.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12324]
    centre_nonneg := (scalarRow12324.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12324]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12324
