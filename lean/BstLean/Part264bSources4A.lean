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
namespace BstLean.Part264b.N12325
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12325 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12325 12325 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12325.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12325 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12325 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12325 := gPlus_lower 12325
end BstLean.Part264b.N12325

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12325
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036354731539 : ℝ) ≤ wn 12325 := by
  have hn : √(12325 : ℝ) ≤ 111.018016555873 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12325 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.018016555873 ≤ 2 / √12325 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259681277 : ℝ) ≤ rhoBar 12325 BstLean.Part154.csC ∧
    rhoBar 12325 BstLean.Part154.csC ≤ 0.000259719332 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036354731539 : ℝ) / (1.295212 * 12325) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12325) := by gcongr
      _ ≤ (0.000259719332 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12325 BstLean.Part154.csC) ≤ 0.001038944783 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12325 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12325 BstLean.Part154.csC) (piBar (rhoBar 12325 BstLean.Part154.csC)) ≤ 0.000198375665 ∧
    cc1 (rhoBar 12325 BstLean.Part154.csC) (piBar (rhoBar 12325 BstLean.Part154.csC)) ≤ 0.000126227694 ∧
    cc2 (rhoBar 12325 BstLean.Part154.csC) ≤ 0.000073276072 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12325 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12325 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12325 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12325 BstLean.Part154.csC * nuR (rhoBar 12325 BstLean.Part154.csC)) ≤ 0.000519455528 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259719332 : ℝ) * 0.001038944783 := by gcongr
      _ ≤ (0.000519455528 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12325 BstLean.Part154.csC) * nuR (rhoBar 12325 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038944783 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12325 BstLean.Part154.csC) * rhoBar 12325 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259719332 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259719332 / 2 + 0.399 * 0.001038944783 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198375665 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519455528 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126227694 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259719332 / 1.414213562 := by gcongr
      _ ≤ (0.000073276072 : ℝ) := by norm_num

end BstLean.Part264b.N12325

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12325
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12325 BstLean.Part154.csC) (piBar (rhoBar 12325 BstLean.Part154.csC)) ≤ 1.69946E-7 := by
  have hr0 : 0 ≤ rhoBar 12325 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12325 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12325 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12325 BstLean.Part154.csC) (piBar (rhoBar 12325 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12325 BstLean.Part154.csC) (piBar (rhoBar 12325 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12325 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198375665 : ℝ) ^ 2 + 0.000126227694 ^ 2 + 3 * 0.000073276072 ^ 2 +
        2 * 0.797885 * 0.000198375665 * 0.000126227694 + 2 * 0.000198375665 * 0.000073276072 +
        4 * 0.797885 * 0.000126227694 * 0.000073276072 := by gcongr
    _ ≤ (1.69946E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12325 BstLean.Part154.csC Θ ≤ 0.002713324284 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12325 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12325 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12325 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12325 BstLean.Part154.csC) (piBar (rhoBar 12325 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12325 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69946E-7 / (0.000259681277 : ℝ) := by gcongr
    _ ≤ 0.002713324284 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12325 BstLean.Part154.csC Θ ≤ 0.003012168629 + 0.000685513297 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12325 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12325 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12325 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259719332 +
        (6863 / 10000) * 0.000259719332 * 12325 * 0.001038944783) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003012168629 + 0.000685513297 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12325 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12325 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12325 0.011 Θ ∧ gammaRatio 12325 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12325 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12325) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12325 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12325 0.011 Θ) :=
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
    badAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12325 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12325 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12325 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12325 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12325 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12325 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12325 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12325 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12325 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12325 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12325 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004112168629 + 0.003398837581 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12325

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12325
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12325 BstLean.Part154.csC) (piBar (rhoBar 12325 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12325 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12325 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12325 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12325 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12325 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12325 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12325 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12325 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12325 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12325 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12325 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12325 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053285495776 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12325) ≤ 0.010757151120 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12325 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010757151120 + 2 * 0.737676 / 12325) := by gcongr
    _ ≤ (0.053285495776 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12325 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12325

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12325
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486093695 : ℝ) ≤ plow 12325 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12325) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403158360)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424495250) : eMP 12325 0.011 xi bn ≤ 0.001225599649 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12325 : ℝ) * (1 - 0.011))) ≤ 0.000605917999 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001424495250 / (12325 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605917999 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605917999 : ℝ) + 3.141593 * 0.053403158360 / (12325 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225599649 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403158360)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424495250) : PiBarMP 12325 12 0.011 xi bn ≤ 0.163720604502 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12325 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037742486008 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.405729018017 : ℝ) ≤ √((12325 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.018016555872 : ℝ) ≤ √12325 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12325) ≤ 0.125496822003 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037742486008 + 0.053403158360 * 1.772454 / (2 * (110.405729018017 : ℝ))) * (1 + 0.001225599649) +
        8 / (12325 * 111.018016555872) + 0.125496822003 := by gcongr
    _ ≤ (0.163720604502 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403158360)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424495250) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284376729621) :
    parallelOracle 12325 0.011 xi bn cd ≤ 0.164744553003 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12325 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12325 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486093695 : ℝ) ≤ plow 12325 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.018016555872 : ℝ) ≤ √12325 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284376729621 : ℝ) / (2 * 0.560486093695 * 111.018016555872)) * 0.163720604502 +
        0.284376729621 ^ 2 / (2 * 0.560486093695 * 111.018016555872) := by gcongr
    _ ≤ (0.164744553003 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053403158360) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424495250)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284376729621) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12325 12325 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486093695 : ℝ) ≤ plow 12325 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.018016555872 : ℝ) ≤ √12325 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12325 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12325 Θ 1.22 ≤ 0.011944912557 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.018016555872 := by gcongr <;> linarith
      _ ≤ (0.011944912557 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12325 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12325 12325 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12325 12325 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12325 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12325 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12325 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12325 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164744553003 + 0.011944912557 + (0.008646 : ℝ) *
        (1 + 2 * (0.284376729621 + 0.011944912557) / (0.560486093695 * 111.018016555872))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12325]

end BstLean.Part264b.N12325

/-! The original eight local profiles supply actual 12325 moment certificates. -/
namespace BstLean.Part264b.N12325
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12325 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053403158360 ∧
    0 ≤ bN 12325 BstLean.Part154.csC (groupTheta g) ∧ bN 12325 BstLean.Part154.csC (groupTheta g) ≤ 0.001424495250 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12325 12325 0.011
      (momentAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12325 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12325 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12325 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231091233845 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12325 0.011
      (momentAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12325 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12325
/-! The actual computed-centre upper energy formula at 12325. -/
namespace BstLean.Part264b.N12325
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12325

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12325
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12325 cell12325)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086671025945
  | 2 => 0.087637574256
  | 3 => 0.088606061473
  | 4 => 0.089578754170
  | 5 => 0.090558361219
  | 6 => 0.091548095094
  | 7 => 0.092551738157
  | 8 => 0.093573713843
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12325 12325 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12325 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12325

/-! Actual upper energy certificates on all 43 source endpoints at 12325. -/
namespace BstLean.Part264b.N12325
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12325 cell12325)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12325 (gMinus 12325) (1 - (cell12325 i).lower) ≤ 1 ∧
    energyUpper 12325 (gMinus 12325) (BstLean.Part211.gPlus 12325)
      (finiteEnergy 12325 12325 0.011) (1 - (cell12325 i).lower) ≤
      (cell12325 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12325) (by norm_num)
        (q := 1 - (cell12325 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12325,cell12325]) (by norm_num [scalarRow12325,cell12325])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12325,cell12325])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12325

/-! Source-cell containment and simple scalar guards at 12325. -/
namespace BstLean.Part264b.N12325
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12325 cell12325)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12325 ⟨10,by decide⟩).lower ∧ (cell12325 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12325 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12325 ⟨11,by decide⟩).lower ∧ (cell12325 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12325 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12325 ⟨12,by decide⟩).lower ∧ (cell12325 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12325 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12325 ⟨13,by decide⟩).lower ∧ (cell12325 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12325 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12325 ⟨14,by decide⟩).lower ∧ (cell12325 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12325 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12325 ⟨15,by decide⟩).lower ∧ (cell12325 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12325 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12325 ⟨16,by decide⟩).lower ∧ (cell12325 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12325 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12325 ⟨17,by decide⟩).lower ∧ (cell12325 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12325 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12325 ⟨18,by decide⟩).lower ∧ (cell12325 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12325 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12325 ⟨19,by decide⟩).lower ∧ (cell12325 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12325 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12325 ⟨20,by decide⟩).lower ∧ (cell12325 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12325 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12325 ⟨21,by decide⟩).lower ∧ (cell12325 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12325 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12325 ⟨22,by decide⟩).lower ∧ (cell12325 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12325 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12325 ⟨23,by decide⟩).lower ∧ (cell12325 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12325 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12325 ⟨24,by decide⟩).lower ∧ (cell12325 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12325 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12325 ⟨25,by decide⟩).lower ∧ (cell12325 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12325 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12325 ⟨26,by decide⟩).lower ∧ (cell12325 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12325 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12325 ⟨27,by decide⟩).lower ∧ (cell12325 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12325 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12325 ⟨28,by decide⟩).lower ∧ (cell12325 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12325 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12325 ⟨29,by decide⟩).lower ∧ (cell12325 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12325 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12325 ⟨30,by decide⟩).lower ∧ (cell12325 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12325 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12325 ⟨31,by decide⟩).lower ∧ (cell12325 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12325 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12325 ⟨32,by decide⟩).lower ∧ (cell12325 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12325 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12325 ⟨33,by decide⟩).lower ∧ (cell12325 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12325 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12325 ⟨34,by decide⟩).lower ∧ (cell12325 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12325 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12325 ⟨35,by decide⟩).lower ∧ (cell12325 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12325 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12325 ⟨36,by decide⟩).lower ∧ (cell12325 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12325 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12325 ⟨37,by decide⟩).lower ∧ (cell12325 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12325 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12325 ⟨38,by decide⟩).lower ∧ (cell12325 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12325 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12325 ⟨39,by decide⟩).lower ∧ (cell12325 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12325 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12325 ⟨40,by decide⟩).lower ∧ (cell12325 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12325 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12325 ⟨41,by decide⟩).lower ∧ (cell12325 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12325 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12325 ⟨42,by decide⟩).lower ∧ (cell12325 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12325 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12325 ⟨43,by decide⟩).lower ∧ (cell12325 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12325 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12325 ⟨44,by decide⟩).lower ∧ (cell12325 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12325 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12325 ⟨45,by decide⟩).lower ∧ (cell12325 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12325 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12325 ⟨46,by decide⟩).lower ∧ (cell12325 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12325 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12325 ⟨47,by decide⟩).lower ∧ (cell12325 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12325 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12325 ⟨48,by decide⟩).lower ∧ (cell12325 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12325 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12325 ⟨49,by decide⟩).lower ∧ (cell12325 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12325 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12325 ⟨50,by decide⟩).lower ∧ (cell12325 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12325 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12325 ⟨51,by decide⟩).lower ∧ (cell12325 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12325 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12325 ⟨52,by decide⟩).lower ∧ (cell12325 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12325 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12325 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12325 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12325,cell12325,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12325 i).lower ∧
    (cell12325 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12325 i).upper ≤ (0.532 : ℝ) ∧
    (cell12325 i).centre ≤ (0.1 : ℝ) ∧ (cell12325 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12325 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12325 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12325

/-! The local source numeric instances at 12325 have no network premises. -/
namespace BstLean.Part264b.N12325
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12325 cell12325)

noncomputable def sourceNumerics12325 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12325 (cell12325 i)
      scalarRow12325.M scalarRow12325.H scalarRow12325.xi := by
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
    energy_allowance := scalarRow12325.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12325]
    centre_nonneg := (scalarRow12325.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12325]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12325
/-! Actual 12326 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12326
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12326 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12326 12326 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12326.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12326 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12326 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12326 := gPlus_lower 12326
end BstLean.Part264b.N12326

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12326
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036353243627 : ℝ) ≤ wn 12326 := by
  have hn : √(12326 : ℝ) ≤ 111.022520238013 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12326 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.022520238013 ≤ 2 / √12326 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259659836 : ℝ) ≤ rhoBar 12326 BstLean.Part154.csC ∧
    rhoBar 12326 BstLean.Part154.csC ≤ 0.000259698261 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036353243627 : ℝ) / (1.295212 * 12326) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12326) := by gcongr
      _ ≤ (0.000259698261 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12326 BstLean.Part154.csC) ≤ 0.001038860488 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12326 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12326 BstLean.Part154.csC) (piBar (rhoBar 12326 BstLean.Part154.csC)) ≤ 0.000198359570 ∧
    cc1 (rhoBar 12326 BstLean.Part154.csC) (piBar (rhoBar 12326 BstLean.Part154.csC)) ≤ 0.000126217453 ∧
    cc2 (rhoBar 12326 BstLean.Part154.csC) ≤ 0.000073270127 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12326 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12326 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12326 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12326 BstLean.Part154.csC * nuR (rhoBar 12326 BstLean.Part154.csC)) ≤ 0.000519413383 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259698261 : ℝ) * 0.001038860488 := by gcongr
      _ ≤ (0.000519413383 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12326 BstLean.Part154.csC) * nuR (rhoBar 12326 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038860488 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12326 BstLean.Part154.csC) * rhoBar 12326 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259698261 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259698261 / 2 + 0.399 * 0.001038860488 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198359570 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519413383 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126217453 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259698261 / 1.414213562 := by gcongr
      _ ≤ (0.000073270127 : ℝ) := by norm_num

end BstLean.Part264b.N12326

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12326
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12326 BstLean.Part154.csC) (piBar (rhoBar 12326 BstLean.Part154.csC)) ≤ 1.69919E-7 := by
  have hr0 : 0 ≤ rhoBar 12326 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12326 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12326 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12326 BstLean.Part154.csC) (piBar (rhoBar 12326 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12326 BstLean.Part154.csC) (piBar (rhoBar 12326 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12326 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198359570 : ℝ) ^ 2 + 0.000126217453 ^ 2 + 3 * 0.000073270127 ^ 2 +
        2 * 0.797885 * 0.000198359570 * 0.000126217453 + 2 * 0.000198359570 * 0.000073270127 +
        4 * 0.797885 * 0.000126217453 * 0.000073270127 := by gcongr
    _ ≤ (1.69919E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12326 BstLean.Part154.csC Θ ≤ 0.002713117220 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12326 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12326 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12326 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12326 BstLean.Part154.csC) (piBar (rhoBar 12326 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12326 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69919E-7 / (0.000259659836 : ℝ) := by gcongr
    _ ≤ 0.002713117220 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12326 BstLean.Part154.csC Θ ≤ 0.003011924235 + 0.000685457682 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12326 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12326 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12326 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259698261 +
        (6863 / 10000) * 0.000259698261 * 12326 * 0.001038860488) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003011924235 + 0.000685457682 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12326 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12326 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12326 0.011 Θ ∧ gammaRatio 12326 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12326 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12326) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12326 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12326 0.011 Θ) :=
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
    badAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12326 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12326 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12326 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12326 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12326 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12326 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12326 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12326 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12326 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12326 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12326 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004111924235 + 0.003398574902 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12326

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12326
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12326 BstLean.Part154.csC) (piBar (rhoBar 12326 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12326 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12326 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12326 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12326 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12326 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12326 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12326 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12326 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12326 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12326 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12326 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12326 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053283310436 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12326) ≤ 0.010756714751 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12326 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010756714751 + 2 * 0.737676 / 12326) := by gcongr
    _ ≤ (0.053283310436 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12326 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12326

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12326
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486141708 : ℝ) ≤ plow 12326 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12326) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402776059)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424386541) : eMP 12326 0.011 xi bn ≤ 0.001225503036 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12326 : ℝ) * (1 - 0.011))) ≤ 0.000605870300 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001424386541 / (12326 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605870300 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605870300 : ℝ) + 3.141593 * 0.053402776059 / (12326 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225503036 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402776059)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424386541) : PiBarMP 12326 12 0.011 xi bn ≤ 0.163714046847 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12326 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037741045839 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.410207861411 : ℝ) ≤ √((12326 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.022520238012 : ℝ) ≤ √12326 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12326) ≤ 0.125491731164 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037741045839 + 0.053402776059 * 1.772454 / (2 * (110.410207861411 : ℝ))) * (1 + 0.001225503036) +
        8 / (12326 * 111.022520238012) + 0.125491731164 := by gcongr
    _ ≤ (0.163714046847 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402776059)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424386541) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284373717115) :
    parallelOracle 12326 0.011 xi bn cd ≤ 0.164737921009 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12326 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12326 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486141708 : ℝ) ≤ plow 12326 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.022520238012 : ℝ) ≤ √12326 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284373717115 : ℝ) / (2 * 0.560486141708 * 111.022520238012)) * 0.163714046847 +
        0.284373717115 ^ 2 / (2 * 0.560486141708 * 111.022520238012) := by gcongr
    _ ≤ (0.164737921009 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402776059) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424386541)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284373717115) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12326 12326 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486141708 : ℝ) ≤ plow 12326 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.022520238012 : ℝ) ≤ √12326 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12326 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12326 Θ 1.22 ≤ 0.011944428006 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.022520238012 := by gcongr <;> linarith
      _ ≤ (0.011944428006 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12326 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12326 12326 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12326 12326 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12326 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12326 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12326 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12326 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164737921009 + 0.011944428006 + (0.008646 : ℝ) *
        (1 + 2 * (0.284373717115 + 0.011944428006) / (0.560486141708 * 111.022520238012))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12326]

end BstLean.Part264b.N12326

/-! The original eight local profiles supply actual 12326 moment certificates. -/
namespace BstLean.Part264b.N12326
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12326 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053402776059 ∧
    0 ≤ bN 12326 BstLean.Part154.csC (groupTheta g) ∧ bN 12326 BstLean.Part154.csC (groupTheta g) ≤ 0.001424386541 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12326 12326 0.011
      (momentAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12326 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12326 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12326 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231090406679 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12326 0.011
      (momentAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12326 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12326
/-! The actual computed-centre upper energy formula at 12326. -/
namespace BstLean.Part264b.N12326
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12326

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12326
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12326 cell12326)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086667612599
  | 2 => 0.087634085841
  | 3 => 0.088602485152
  | 4 => 0.089575074312
  | 5 => 0.090554558935
  | 6 => 0.091544147721
  | 7 => 0.092547618685
  | 8 => 0.093569390287
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12326 12326 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12326 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12326

/-! Actual upper energy certificates on all 43 source endpoints at 12326. -/
namespace BstLean.Part264b.N12326
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12326 cell12326)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12326 (gMinus 12326) (1 - (cell12326 i).lower) ≤ 1 ∧
    energyUpper 12326 (gMinus 12326) (BstLean.Part211.gPlus 12326)
      (finiteEnergy 12326 12326 0.011) (1 - (cell12326 i).lower) ≤
      (cell12326 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12326) (by norm_num)
        (q := 1 - (cell12326 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12326,cell12326]) (by norm_num [scalarRow12326,cell12326])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12326,cell12326])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12326

/-! Source-cell containment and simple scalar guards at 12326. -/
namespace BstLean.Part264b.N12326
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12326 cell12326)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12326 ⟨10,by decide⟩).lower ∧ (cell12326 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12326 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12326 ⟨11,by decide⟩).lower ∧ (cell12326 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12326 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12326 ⟨12,by decide⟩).lower ∧ (cell12326 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12326 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12326 ⟨13,by decide⟩).lower ∧ (cell12326 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12326 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12326 ⟨14,by decide⟩).lower ∧ (cell12326 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12326 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12326 ⟨15,by decide⟩).lower ∧ (cell12326 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12326 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12326 ⟨16,by decide⟩).lower ∧ (cell12326 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12326 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12326 ⟨17,by decide⟩).lower ∧ (cell12326 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12326 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12326 ⟨18,by decide⟩).lower ∧ (cell12326 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12326 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12326 ⟨19,by decide⟩).lower ∧ (cell12326 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12326 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12326 ⟨20,by decide⟩).lower ∧ (cell12326 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12326 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12326 ⟨21,by decide⟩).lower ∧ (cell12326 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12326 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12326 ⟨22,by decide⟩).lower ∧ (cell12326 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12326 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12326 ⟨23,by decide⟩).lower ∧ (cell12326 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12326 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12326 ⟨24,by decide⟩).lower ∧ (cell12326 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12326 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12326 ⟨25,by decide⟩).lower ∧ (cell12326 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12326 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12326 ⟨26,by decide⟩).lower ∧ (cell12326 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12326 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12326 ⟨27,by decide⟩).lower ∧ (cell12326 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12326 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12326 ⟨28,by decide⟩).lower ∧ (cell12326 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12326 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12326 ⟨29,by decide⟩).lower ∧ (cell12326 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12326 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12326 ⟨30,by decide⟩).lower ∧ (cell12326 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12326 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12326 ⟨31,by decide⟩).lower ∧ (cell12326 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12326 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12326 ⟨32,by decide⟩).lower ∧ (cell12326 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12326 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12326 ⟨33,by decide⟩).lower ∧ (cell12326 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12326 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12326 ⟨34,by decide⟩).lower ∧ (cell12326 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12326 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12326 ⟨35,by decide⟩).lower ∧ (cell12326 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12326 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12326 ⟨36,by decide⟩).lower ∧ (cell12326 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12326 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12326 ⟨37,by decide⟩).lower ∧ (cell12326 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12326 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12326 ⟨38,by decide⟩).lower ∧ (cell12326 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12326 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12326 ⟨39,by decide⟩).lower ∧ (cell12326 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12326 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12326 ⟨40,by decide⟩).lower ∧ (cell12326 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12326 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12326 ⟨41,by decide⟩).lower ∧ (cell12326 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12326 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12326 ⟨42,by decide⟩).lower ∧ (cell12326 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12326 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12326 ⟨43,by decide⟩).lower ∧ (cell12326 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12326 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12326 ⟨44,by decide⟩).lower ∧ (cell12326 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12326 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12326 ⟨45,by decide⟩).lower ∧ (cell12326 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12326 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12326 ⟨46,by decide⟩).lower ∧ (cell12326 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12326 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12326 ⟨47,by decide⟩).lower ∧ (cell12326 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12326 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12326 ⟨48,by decide⟩).lower ∧ (cell12326 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12326 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12326 ⟨49,by decide⟩).lower ∧ (cell12326 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12326 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12326 ⟨50,by decide⟩).lower ∧ (cell12326 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12326 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12326 ⟨51,by decide⟩).lower ∧ (cell12326 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12326 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12326 ⟨52,by decide⟩).lower ∧ (cell12326 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12326 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12326 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12326 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12326,cell12326,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12326 i).lower ∧
    (cell12326 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12326 i).upper ≤ (0.532 : ℝ) ∧
    (cell12326 i).centre ≤ (0.1 : ℝ) ∧ (cell12326 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12326 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12326 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12326

/-! The local source numeric instances at 12326 have no network premises. -/
namespace BstLean.Part264b.N12326
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12326 cell12326)

noncomputable def sourceNumerics12326 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12326 (cell12326 i)
      scalarRow12326.M scalarRow12326.H scalarRow12326.xi := by
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
    energy_allowance := scalarRow12326.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12326]
    centre_nonneg := (scalarRow12326.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12326]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12326
/-! Actual 12327 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12327
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12327 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12327 12327 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12327.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12327 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12327 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12327 := gPlus_lower 12327
end BstLean.Part264b.N12327

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12327
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036351755897 : ℝ) ≤ wn 12327 := by
  have hn : √(12327 : ℝ) ≤ 111.027023737467 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12327 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.027023737467 ≤ 2 / √12327 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259638399 : ℝ) ≤ rhoBar 12327 BstLean.Part154.csC ∧
    rhoBar 12327 BstLean.Part154.csC ≤ 0.000259677193 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036351755897 : ℝ) / (1.295212 * 12327) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12327) := by gcongr
      _ ≤ (0.000259677193 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12327 BstLean.Part154.csC) ≤ 0.001038776205 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12327 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12327 BstLean.Part154.csC) (piBar (rhoBar 12327 BstLean.Part154.csC)) ≤ 0.000198343477 ∧
    cc1 (rhoBar 12327 BstLean.Part154.csC) (piBar (rhoBar 12327 BstLean.Part154.csC)) ≤ 0.000126207213 ∧
    cc2 (rhoBar 12327 BstLean.Part154.csC) ≤ 0.000073264183 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12327 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12327 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12327 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12327 BstLean.Part154.csC * nuR (rhoBar 12327 BstLean.Part154.csC)) ≤ 0.000519371244 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259677193 : ℝ) * 0.001038776205 := by gcongr
      _ ≤ (0.000519371244 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12327 BstLean.Part154.csC) * nuR (rhoBar 12327 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038776205 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12327 BstLean.Part154.csC) * rhoBar 12327 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259677193 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259677193 / 2 + 0.399 * 0.001038776205 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198343477 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519371244 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126207213 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259677193 / 1.414213562 := by gcongr
      _ ≤ (0.000073264183 : ℝ) := by norm_num

end BstLean.Part264b.N12327

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12327
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12327 BstLean.Part154.csC) (piBar (rhoBar 12327 BstLean.Part154.csC)) ≤ 1.69891E-7 := by
  have hr0 : 0 ≤ rhoBar 12327 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12327 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12327 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12327 BstLean.Part154.csC) (piBar (rhoBar 12327 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12327 BstLean.Part154.csC) (piBar (rhoBar 12327 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12327 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198343477 : ℝ) ^ 2 + 0.000126207213 ^ 2 + 3 * 0.000073264183 ^ 2 +
        2 * 0.797885 * 0.000198343477 * 0.000126207213 + 2 * 0.000198343477 * 0.000073264183 +
        4 * 0.797885 * 0.000126207213 * 0.000073264183 := by gcongr
    _ ≤ (1.69891E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12327 BstLean.Part154.csC Θ ≤ 0.002712894112 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12327 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12327 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12327 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12327 BstLean.Part154.csC) (piBar (rhoBar 12327 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12327 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69891E-7 / (0.000259638399 : ℝ) := by gcongr
    _ ≤ 0.002712894112 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12327 BstLean.Part154.csC Θ ≤ 0.003011679870 + 0.000685402074 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12327 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12327 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12327 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259677193 +
        (6863 / 10000) * 0.000259677193 * 12327 * 0.001038776205) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003011679870 + 0.000685402074 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12327 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12327 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12327 0.011 Θ ∧ gammaRatio 12327 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12327 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12327) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12327 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12327 0.011 Θ) :=
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
    badAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12327 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12327 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12327 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12327 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12327 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12327 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12327 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12327 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12327 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12327 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12327 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004111679870 + 0.003398296186 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12327

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12327
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12327 BstLean.Part154.csC) (piBar (rhoBar 12327 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12327 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12327 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12327 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12327 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12327 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12327 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12327 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12327 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12327 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12327 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12327 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12327 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053281125364 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12327) ≤ 0.010756278435 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12327 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010756278435 + 2 * 0.737676 / 12327) := by gcongr
    _ ≤ (0.053281125364 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12327 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12327

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12327
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486189713 : ℝ) ≤ plow 12327 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12327) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402385368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424269409) : eMP 12327 0.011 xi bn ≤ 0.001225402847 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12327 : ℝ) * (1 - 0.011))) ≤ 0.000605820814 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001424269409 / (12327 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605820814 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605820814 : ℝ) + 3.141593 * 0.053402385368 / (12327 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225402847 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402385368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424269409) : PiBarMP 12327 12 0.011 xi bn ≤ 0.163707377825 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12327 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037739494022 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.414686523125 : ℝ) ≤ √((12327 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.027023737466 : ℝ) ≤ √12327 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12327) ≤ 0.125486640944 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037739494022 + 0.053402385368 * 1.772454 / (2 * (110.414686523125 : ℝ))) * (1 + 0.001225402847) +
        8 / (12327 * 111.027023737466) + 0.125486640944 := by gcongr
    _ ≤ (0.163707377825 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402385368)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424269409) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284370686721) :
    parallelOracle 12327 0.011 xi bn cd ≤ 0.164731177296 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12327 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12327 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486189713 : ℝ) ≤ plow 12327 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.027023737466 : ℝ) ≤ √12327 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284370686721 : ℝ) / (2 * 0.560486189713 * 111.027023737466)) * 0.163707377825 +
        0.284370686721 ^ 2 / (2 * 0.560486189713 * 111.027023737466) := by gcongr
    _ ≤ (0.164731177296 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402385368) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424269409)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284370686721) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12327 12327 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486189713 : ℝ) ≤ plow 12327 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.027023737466 : ℝ) ≤ √12327 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12327 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12327 Θ 1.22 ≤ 0.011943943514 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.027023737466 := by gcongr <;> linarith
      _ ≤ (0.011943943514 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12327 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12327 12327 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12327 12327 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12327 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12327 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12327 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12327 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164731177296 + 0.011943943514 + (0.008646 : ℝ) *
        (1 + 2 * (0.284370686721 + 0.011943943514) / (0.560486189713 * 111.027023737466))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12327]

end BstLean.Part264b.N12327

/-! The original eight local profiles supply actual 12327 moment certificates. -/
namespace BstLean.Part264b.N12327
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12327 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053402385368 ∧
    0 ≤ bN 12327 BstLean.Part154.csC (groupTheta g) ∧ bN 12327 BstLean.Part154.csC (groupTheta g) ≤ 0.001424269409 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12327 12327 0.011
      (momentAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12327 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12327 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12327 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231089561357 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12327 0.011
      (momentAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12327 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12327
/-! The actual computed-centre upper energy formula at 12327. -/
namespace BstLean.Part264b.N12327
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12327

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12327
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12327 cell12327)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086664200865
  | 2 => 0.087630599111
  | 3 => 0.088598910606
  | 4 => 0.089571396338
  | 5 => 0.090550758669
  | 6 => 0.091540202527
  | 7 => 0.092543501585
  | 8 => 0.093565069335
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12327 12327 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12327 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12327

/-! Actual upper energy certificates on all 43 source endpoints at 12327. -/
namespace BstLean.Part264b.N12327
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12327 cell12327)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12327 (gMinus 12327) (1 - (cell12327 i).lower) ≤ 1 ∧
    energyUpper 12327 (gMinus 12327) (BstLean.Part211.gPlus 12327)
      (finiteEnergy 12327 12327 0.011) (1 - (cell12327 i).lower) ≤
      (cell12327 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12327) (by norm_num)
        (q := 1 - (cell12327 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12327,cell12327]) (by norm_num [scalarRow12327,cell12327])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12327,cell12327])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12327

/-! Source-cell containment and simple scalar guards at 12327. -/
namespace BstLean.Part264b.N12327
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12327 cell12327)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12327 ⟨10,by decide⟩).lower ∧ (cell12327 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12327 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12327 ⟨11,by decide⟩).lower ∧ (cell12327 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12327 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12327 ⟨12,by decide⟩).lower ∧ (cell12327 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12327 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12327 ⟨13,by decide⟩).lower ∧ (cell12327 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12327 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12327 ⟨14,by decide⟩).lower ∧ (cell12327 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12327 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12327 ⟨15,by decide⟩).lower ∧ (cell12327 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12327 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12327 ⟨16,by decide⟩).lower ∧ (cell12327 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12327 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12327 ⟨17,by decide⟩).lower ∧ (cell12327 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12327 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12327 ⟨18,by decide⟩).lower ∧ (cell12327 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12327 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12327 ⟨19,by decide⟩).lower ∧ (cell12327 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12327 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12327 ⟨20,by decide⟩).lower ∧ (cell12327 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12327 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12327 ⟨21,by decide⟩).lower ∧ (cell12327 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12327 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12327 ⟨22,by decide⟩).lower ∧ (cell12327 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12327 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12327 ⟨23,by decide⟩).lower ∧ (cell12327 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12327 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12327 ⟨24,by decide⟩).lower ∧ (cell12327 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12327 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12327 ⟨25,by decide⟩).lower ∧ (cell12327 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12327 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12327 ⟨26,by decide⟩).lower ∧ (cell12327 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12327 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12327 ⟨27,by decide⟩).lower ∧ (cell12327 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12327 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12327 ⟨28,by decide⟩).lower ∧ (cell12327 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12327 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12327 ⟨29,by decide⟩).lower ∧ (cell12327 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12327 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12327 ⟨30,by decide⟩).lower ∧ (cell12327 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12327 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12327 ⟨31,by decide⟩).lower ∧ (cell12327 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12327 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12327 ⟨32,by decide⟩).lower ∧ (cell12327 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12327 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12327 ⟨33,by decide⟩).lower ∧ (cell12327 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12327 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12327 ⟨34,by decide⟩).lower ∧ (cell12327 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12327 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12327 ⟨35,by decide⟩).lower ∧ (cell12327 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12327 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12327 ⟨36,by decide⟩).lower ∧ (cell12327 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12327 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12327 ⟨37,by decide⟩).lower ∧ (cell12327 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12327 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12327 ⟨38,by decide⟩).lower ∧ (cell12327 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12327 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12327 ⟨39,by decide⟩).lower ∧ (cell12327 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12327 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12327 ⟨40,by decide⟩).lower ∧ (cell12327 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12327 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12327 ⟨41,by decide⟩).lower ∧ (cell12327 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12327 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12327 ⟨42,by decide⟩).lower ∧ (cell12327 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12327 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12327 ⟨43,by decide⟩).lower ∧ (cell12327 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12327 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12327 ⟨44,by decide⟩).lower ∧ (cell12327 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12327 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12327 ⟨45,by decide⟩).lower ∧ (cell12327 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12327 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12327 ⟨46,by decide⟩).lower ∧ (cell12327 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12327 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12327 ⟨47,by decide⟩).lower ∧ (cell12327 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12327 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12327 ⟨48,by decide⟩).lower ∧ (cell12327 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12327 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12327 ⟨49,by decide⟩).lower ∧ (cell12327 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12327 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12327 ⟨50,by decide⟩).lower ∧ (cell12327 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12327 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12327 ⟨51,by decide⟩).lower ∧ (cell12327 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12327 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12327 ⟨52,by decide⟩).lower ∧ (cell12327 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12327 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12327 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12327 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12327,cell12327,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12327 i).lower ∧
    (cell12327 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12327 i).upper ≤ (0.532 : ℝ) ∧
    (cell12327 i).centre ≤ (0.1 : ℝ) ∧ (cell12327 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12327 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12327 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12327

/-! The local source numeric instances at 12327 have no network premises. -/
namespace BstLean.Part264b.N12327
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12327 cell12327)

noncomputable def sourceNumerics12327 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12327 (cell12327 i)
      scalarRow12327.M scalarRow12327.H scalarRow12327.xi := by
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
    energy_allowance := scalarRow12327.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12327]
    centre_nonneg := (scalarRow12327.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12327]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12327
/-! Actual 12328 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12328
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12328 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12328 12328 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12328.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12328 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12328 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12328 := gPlus_lower 12328
end BstLean.Part264b.N12328

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12328
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036350268349 : ℝ) ≤ wn 12328 := by
  have hn : √(12328 : ℝ) ≤ 111.031527054257 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12328 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.031527054257 ≤ 2 / √12328 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259616966 : ℝ) ≤ rhoBar 12328 BstLean.Part154.csC ∧
    rhoBar 12328 BstLean.Part154.csC ≤ 0.000259656129 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036350268349 : ℝ) / (1.295212 * 12328) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12328) := by gcongr
      _ ≤ (0.000259656129 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12328 BstLean.Part154.csC) ≤ 0.001038691938 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12328 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12328 BstLean.Part154.csC) (piBar (rhoBar 12328 BstLean.Part154.csC)) ≤ 0.000198327388 ∧
    cc1 (rhoBar 12328 BstLean.Part154.csC) (piBar (rhoBar 12328 BstLean.Part154.csC)) ≤ 0.000126196975 ∧
    cc2 (rhoBar 12328 BstLean.Part154.csC) ≤ 0.000073258240 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12328 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12328 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12328 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12328 BstLean.Part154.csC * nuR (rhoBar 12328 BstLean.Part154.csC)) ≤ 0.000519329114 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259656129 : ℝ) * 0.001038691938 := by gcongr
      _ ≤ (0.000519329114 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12328 BstLean.Part154.csC) * nuR (rhoBar 12328 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038691938 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12328 BstLean.Part154.csC) * rhoBar 12328 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259656129 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259656129 / 2 + 0.399 * 0.001038691938 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198327388 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519329114 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126196975 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259656129 / 1.414213562 := by gcongr
      _ ≤ (0.000073258240 : ℝ) := by norm_num

end BstLean.Part264b.N12328

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12328
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12328 BstLean.Part154.csC) (piBar (rhoBar 12328 BstLean.Part154.csC)) ≤ 1.69864E-7 := by
  have hr0 : 0 ≤ rhoBar 12328 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12328 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12328 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12328 BstLean.Part154.csC) (piBar (rhoBar 12328 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12328 BstLean.Part154.csC) (piBar (rhoBar 12328 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12328 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198327388 : ℝ) ^ 2 + 0.000126196975 ^ 2 + 3 * 0.000073258240 ^ 2 +
        2 * 0.797885 * 0.000198327388 * 0.000126196975 + 2 * 0.000198327388 * 0.000073258240 +
        4 * 0.797885 * 0.000126196975 * 0.000073258240 := by gcongr
    _ ≤ (1.69864E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12328 BstLean.Part154.csC Θ ≤ 0.002712686895 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12328 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12328 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12328 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12328 BstLean.Part154.csC) (piBar (rhoBar 12328 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12328 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69864E-7 / (0.000259616966 : ℝ) := by gcongr
    _ ≤ 0.002712686895 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12328 BstLean.Part154.csC Θ ≤ 0.003011435558 + 0.000685346477 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12328 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12328 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12328 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259656129 +
        (6863 / 10000) * 0.000259656129 * 12328 * 0.001038691938) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003011435558 + 0.000685346477 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12328 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12328 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12328 0.011 Θ ∧ gammaRatio 12328 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12328 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12328) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12328 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12328 0.011 Θ) :=
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
    badAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12328 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12328 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12328 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12328 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12328 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12328 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12328 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12328 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12328 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12328 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12328 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004111435558 + 0.003398033372 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12328

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12328
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12328 BstLean.Part154.csC) (piBar (rhoBar 12328 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12328 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12328 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12328 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12328 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12328 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12328 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12328 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12328 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12328 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12328 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12328 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12328 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053278940559 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12328) ≤ 0.010755842172 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12328 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010755842172 + 2 * 0.737676 / 12328) := by gcongr
    _ ≤ (0.053278940559 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12328 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12328

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12328
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486237710 : ℝ) ≤ plow 12328 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12328) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402003079)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424160620) : eMP 12328 0.011 xi bn ≤ 0.001225306216 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12328 : ℝ) * (1 - 0.011))) ≤ 0.000605773106 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001424160620 / (12328 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605773106 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605773106 : ℝ) + 3.141593 * 0.053402003079 / (12328 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225306216 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402003079)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424160620) : PiBarMP 12328 12 0.011 xi bn ≤ 0.163700820239 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12328 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037738052679 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.419165003182 : ℝ) ≤ √((12328 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.031527054256 : ℝ) ≤ √12328 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12328) ≤ 0.125481551344 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037738052679 + 0.053402003079 * 1.772454 / (2 * (110.419165003182 : ℝ))) * (1 + 0.001225306216) +
        8 / (12328 * 111.031527054256) + 0.125481551344 := by gcongr
    _ ≤ (0.163700820239 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402003079)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424160620) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284367674770) :
    parallelOracle 12328 0.011 xi bn cd ≤ 0.164724545391 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12328 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12328 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486237710 : ℝ) ≤ plow 12328 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.031527054256 : ℝ) ≤ √12328 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284367674770 : ℝ) / (2 * 0.560486237710 * 111.031527054256)) * 0.163700820239 +
        0.284367674770 ^ 2 / (2 * 0.560486237710 * 111.031527054256) := by gcongr
    _ ≤ (0.164724545391 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053402003079) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424160620)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284367674770) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12328 12328 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486237710 : ℝ) ≤ plow 12328 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.031527054256 : ℝ) ≤ √12328 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12328 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12328 Θ 1.22 ≤ 0.011943459081 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.031527054256 := by gcongr <;> linarith
      _ ≤ (0.011943459081 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12328 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12328 12328 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12328 12328 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12328 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12328 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12328 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12328 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164724545391 + 0.011943459081 + (0.008646 : ℝ) *
        (1 + 2 * (0.284367674770 + 0.011943459081) / (0.560486237710 * 111.031527054256))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12328]

end BstLean.Part264b.N12328

/-! The original eight local profiles supply actual 12328 moment certificates. -/
namespace BstLean.Part264b.N12328
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12328 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053402003079 ∧
    0 ≤ bN 12328 BstLean.Part154.csC (groupTheta g) ∧ bN 12328 BstLean.Part154.csC (groupTheta g) ≤ 0.001424160620 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12328 12328 0.011
      (momentAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12328 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12328 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12328 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231088734211 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12328 0.011
      (momentAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12328 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12328
/-! The actual computed-centre upper energy formula at 12328. -/
namespace BstLean.Part264b.N12328
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12328

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12328
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12328 cell12328)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086660790742
  | 2 => 0.087627114064
  | 3 => 0.088595337832
  | 4 => 0.089567720246
  | 5 => 0.090546960418
  | 6 => 0.091536259509
  | 7 => 0.092539386855
  | 8 => 0.093560750985
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12328 12328 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12328 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12328

/-! Actual upper energy certificates on all 43 source endpoints at 12328. -/
namespace BstLean.Part264b.N12328
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12328 cell12328)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12328 (gMinus 12328) (1 - (cell12328 i).lower) ≤ 1 ∧
    energyUpper 12328 (gMinus 12328) (BstLean.Part211.gPlus 12328)
      (finiteEnergy 12328 12328 0.011) (1 - (cell12328 i).lower) ≤
      (cell12328 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12328) (by norm_num)
        (q := 1 - (cell12328 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12328,cell12328]) (by norm_num [scalarRow12328,cell12328])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12328,cell12328])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12328

/-! Source-cell containment and simple scalar guards at 12328. -/
namespace BstLean.Part264b.N12328
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12328 cell12328)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12328 ⟨10,by decide⟩).lower ∧ (cell12328 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12328 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12328 ⟨11,by decide⟩).lower ∧ (cell12328 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12328 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12328 ⟨12,by decide⟩).lower ∧ (cell12328 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12328 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12328 ⟨13,by decide⟩).lower ∧ (cell12328 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12328 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12328 ⟨14,by decide⟩).lower ∧ (cell12328 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12328 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12328 ⟨15,by decide⟩).lower ∧ (cell12328 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12328 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12328 ⟨16,by decide⟩).lower ∧ (cell12328 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12328 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12328 ⟨17,by decide⟩).lower ∧ (cell12328 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12328 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12328 ⟨18,by decide⟩).lower ∧ (cell12328 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12328 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12328 ⟨19,by decide⟩).lower ∧ (cell12328 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12328 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12328 ⟨20,by decide⟩).lower ∧ (cell12328 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12328 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12328 ⟨21,by decide⟩).lower ∧ (cell12328 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12328 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12328 ⟨22,by decide⟩).lower ∧ (cell12328 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12328 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12328 ⟨23,by decide⟩).lower ∧ (cell12328 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12328 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12328 ⟨24,by decide⟩).lower ∧ (cell12328 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12328 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12328 ⟨25,by decide⟩).lower ∧ (cell12328 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12328 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12328 ⟨26,by decide⟩).lower ∧ (cell12328 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12328 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12328 ⟨27,by decide⟩).lower ∧ (cell12328 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12328 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12328 ⟨28,by decide⟩).lower ∧ (cell12328 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12328 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12328 ⟨29,by decide⟩).lower ∧ (cell12328 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12328 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12328 ⟨30,by decide⟩).lower ∧ (cell12328 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12328 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12328 ⟨31,by decide⟩).lower ∧ (cell12328 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12328 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12328 ⟨32,by decide⟩).lower ∧ (cell12328 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12328 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12328 ⟨33,by decide⟩).lower ∧ (cell12328 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12328 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12328 ⟨34,by decide⟩).lower ∧ (cell12328 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12328 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12328 ⟨35,by decide⟩).lower ∧ (cell12328 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12328 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12328 ⟨36,by decide⟩).lower ∧ (cell12328 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12328 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12328 ⟨37,by decide⟩).lower ∧ (cell12328 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12328 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12328 ⟨38,by decide⟩).lower ∧ (cell12328 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12328 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12328 ⟨39,by decide⟩).lower ∧ (cell12328 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12328 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12328 ⟨40,by decide⟩).lower ∧ (cell12328 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12328 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12328 ⟨41,by decide⟩).lower ∧ (cell12328 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12328 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12328 ⟨42,by decide⟩).lower ∧ (cell12328 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12328 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12328 ⟨43,by decide⟩).lower ∧ (cell12328 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12328 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12328 ⟨44,by decide⟩).lower ∧ (cell12328 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12328 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12328 ⟨45,by decide⟩).lower ∧ (cell12328 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12328 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12328 ⟨46,by decide⟩).lower ∧ (cell12328 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12328 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12328 ⟨47,by decide⟩).lower ∧ (cell12328 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12328 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12328 ⟨48,by decide⟩).lower ∧ (cell12328 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12328 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12328 ⟨49,by decide⟩).lower ∧ (cell12328 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12328 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12328 ⟨50,by decide⟩).lower ∧ (cell12328 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12328 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12328 ⟨51,by decide⟩).lower ∧ (cell12328 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12328 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12328 ⟨52,by decide⟩).lower ∧ (cell12328 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12328 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12328 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12328 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12328,cell12328,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12328 i).lower ∧
    (cell12328 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12328 i).upper ≤ (0.532 : ℝ) ∧
    (cell12328 i).centre ≤ (0.1 : ℝ) ∧ (cell12328 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12328 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12328 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12328

/-! The local source numeric instances at 12328 have no network premises. -/
namespace BstLean.Part264b.N12328
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12328 cell12328)

noncomputable def sourceNumerics12328 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12328 (cell12328 i)
      scalarRow12328.M scalarRow12328.H scalarRow12328.xi := by
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
    energy_allowance := scalarRow12328.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12328]
    centre_nonneg := (scalarRow12328.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12328]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12328
/-! Actual 12329 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12329
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12329 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12329 12329 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12329.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12329 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12329 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12329 := gPlus_lower 12329
end BstLean.Part264b.N12329

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12329
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036348780984 : ℝ) ≤ wn 12329 := by
  have hn : √(12329 : ℝ) ≤ 111.036030188404 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12329 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.036030188404 ≤ 2 / √12329 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259595536 : ℝ) ≤ rhoBar 12329 BstLean.Part154.csC ∧
    rhoBar 12329 BstLean.Part154.csC ≤ 0.000259635069 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036348780984 : ℝ) / (1.295212 * 12329) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12329) := by gcongr
      _ ≤ (0.000259635069 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12329 BstLean.Part154.csC) ≤ 0.001038607687 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12329 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12329 BstLean.Part154.csC) (piBar (rhoBar 12329 BstLean.Part154.csC)) ≤ 0.000198311301 ∧
    cc1 (rhoBar 12329 BstLean.Part154.csC) (piBar (rhoBar 12329 BstLean.Part154.csC)) ≤ 0.000126186739 ∧
    cc2 (rhoBar 12329 BstLean.Part154.csC) ≤ 0.000073252298 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12329 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12329 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12329 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12329 BstLean.Part154.csC * nuR (rhoBar 12329 BstLean.Part154.csC)) ≤ 0.000519286991 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259635069 : ℝ) * 0.001038607687 := by gcongr
      _ ≤ (0.000519286991 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12329 BstLean.Part154.csC) * nuR (rhoBar 12329 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038607687 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12329 BstLean.Part154.csC) * rhoBar 12329 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259635069 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259635069 / 2 + 0.399 * 0.001038607687 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198311301 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519286991 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126186739 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259635069 / 1.414213562 := by gcongr
      _ ≤ (0.000073252298 : ℝ) := by norm_num

end BstLean.Part264b.N12329

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12329
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12329 BstLean.Part154.csC) (piBar (rhoBar 12329 BstLean.Part154.csC)) ≤ 1.69836E-7 := by
  have hr0 : 0 ≤ rhoBar 12329 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12329 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12329 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12329 BstLean.Part154.csC) (piBar (rhoBar 12329 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12329 BstLean.Part154.csC) (piBar (rhoBar 12329 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12329 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198311301 : ℝ) ^ 2 + 0.000126186739 ^ 2 + 3 * 0.000073252298 ^ 2 +
        2 * 0.797885 * 0.000198311301 * 0.000126186739 + 2 * 0.000198311301 * 0.000073252298 +
        4 * 0.797885 * 0.000126186739 * 0.000073252298 := by gcongr
    _ ≤ (1.69836E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12329 BstLean.Part154.csC Θ ≤ 0.002712463641 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12329 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12329 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12329 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12329 BstLean.Part154.csC) (piBar (rhoBar 12329 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12329 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69836E-7 / (0.000259595536 : ℝ) := by gcongr
    _ ≤ 0.002712463641 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12329 BstLean.Part154.csC Θ ≤ 0.003011191300 + 0.000685290890 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12329 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12329 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12329 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259635069 +
        (6863 / 10000) * 0.000259635069 * 12329 * 0.001038607687) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003011191300 + 0.000685290890 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12329 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12329 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12329 0.011 Θ ∧ gammaRatio 12329 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12329 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12329) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12329 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12329 0.011 Θ) :=
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
    badAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12329 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12329 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12329 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12329 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12329 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12329 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12329 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12329 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12329 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12329 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12329 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004111191300 + 0.003397754531 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12329

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12329
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12329 BstLean.Part154.csC) (piBar (rhoBar 12329 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12329 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12329 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12329 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12329 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12329 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12329 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12329 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12329 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12329 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12329 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12329 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12329 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053276756022 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12329) ≤ 0.010755405962 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12329 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010755405962 + 2 * 0.737676 / 12329) := by gcongr
    _ ≤ (0.053276756022 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12329 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12329

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12329
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486285700 : ℝ) ≤ plow 12329 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12329) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053401612429)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424043412) : eMP 12329 0.011 xi bn ≤ 0.001225206009 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12329 : ℝ) * (1 - 0.011))) ≤ 0.000605723611 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001424043412 / (12329 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605723611 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605723611 : ℝ) + 3.141593 * 0.053401612429 / (12329 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225206009 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053401612429)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424043412) : PiBarMP 12329 12 0.011 xi bn ≤ 0.163694151329 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12329 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037736499732 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.423643301604 : ℝ) ≤ √((12329 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.036030188403 : ℝ) ≤ √12329 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12329) ≤ 0.125476462362 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037736499732 + 0.053401612429 * 1.772454 / (2 * (110.423643301604 : ℝ))) * (1 + 0.001225206009) +
        8 / (12329 * 111.036030188403) + 0.125476462362 := by gcongr
    _ ≤ (0.163694151329 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053401612429)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424043412) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284364644993) :
    parallelOracle 12329 0.011 xi bn cd ≤ 0.164717801811 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12329 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12329 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486285700 : ℝ) ≤ plow 12329 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.036030188403 : ℝ) ≤ √12329 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284364644993 : ℝ) / (2 * 0.560486285700 * 111.036030188403)) * 0.163694151329 +
        0.284364644993 ^ 2 / (2 * 0.560486285700 * 111.036030188403) := by gcongr
    _ ≤ (0.164717801811 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053401612429) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001424043412)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284364644993) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12329 12329 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486285700 : ℝ) ≤ plow 12329 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.036030188403 : ℝ) ≤ √12329 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12329 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12329 Θ 1.22 ≤ 0.011942974707 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.036030188403 := by gcongr <;> linarith
      _ ≤ (0.011942974707 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12329 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12329 12329 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12329 12329 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12329 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12329 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12329 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12329 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164717801811 + 0.011942974707 + (0.008646 : ℝ) *
        (1 + 2 * (0.284364644993 + 0.011942974707) / (0.560486285700 * 111.036030188403))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12329]

end BstLean.Part264b.N12329

/-! The original eight local profiles supply actual 12329 moment certificates. -/
namespace BstLean.Part264b.N12329
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12329 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053401612429 ∧
    0 ≤ bN 12329 BstLean.Part154.csC (groupTheta g) ∧ bN 12329 BstLean.Part154.csC (groupTheta g) ≤ 0.001424043412 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12329 12329 0.011
      (momentAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12329 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12329 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12329 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231087888971 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12329 0.011
      (momentAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12329 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12329
/-! The actual computed-centre upper energy formula at 12329. -/
namespace BstLean.Part264b.N12329
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12329

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12329
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12329 cell12329)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086657382228
  | 2 => 0.087623630699
  | 3 => 0.088591766828
  | 4 => 0.089564046034
  | 5 => 0.090543164180
  | 6 => 0.091532318665
  | 7 => 0.092535274493
  | 8 => 0.093556435234
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12329 12329 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12329 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12329

/-! Actual upper energy certificates on all 43 source endpoints at 12329. -/
namespace BstLean.Part264b.N12329
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12329 cell12329)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12329 (gMinus 12329) (1 - (cell12329 i).lower) ≤ 1 ∧
    energyUpper 12329 (gMinus 12329) (BstLean.Part211.gPlus 12329)
      (finiteEnergy 12329 12329 0.011) (1 - (cell12329 i).lower) ≤
      (cell12329 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12329) (by norm_num)
        (q := 1 - (cell12329 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12329,cell12329]) (by norm_num [scalarRow12329,cell12329])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12329,cell12329])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12329

/-! Source-cell containment and simple scalar guards at 12329. -/
namespace BstLean.Part264b.N12329
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12329 cell12329)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12329 ⟨10,by decide⟩).lower ∧ (cell12329 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12329 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12329 ⟨11,by decide⟩).lower ∧ (cell12329 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12329 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12329 ⟨12,by decide⟩).lower ∧ (cell12329 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12329 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12329 ⟨13,by decide⟩).lower ∧ (cell12329 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12329 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12329 ⟨14,by decide⟩).lower ∧ (cell12329 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12329 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12329 ⟨15,by decide⟩).lower ∧ (cell12329 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12329 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12329 ⟨16,by decide⟩).lower ∧ (cell12329 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12329 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12329 ⟨17,by decide⟩).lower ∧ (cell12329 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12329 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12329 ⟨18,by decide⟩).lower ∧ (cell12329 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12329 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12329 ⟨19,by decide⟩).lower ∧ (cell12329 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12329 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12329 ⟨20,by decide⟩).lower ∧ (cell12329 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12329 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12329 ⟨21,by decide⟩).lower ∧ (cell12329 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12329 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12329 ⟨22,by decide⟩).lower ∧ (cell12329 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12329 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12329 ⟨23,by decide⟩).lower ∧ (cell12329 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12329 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12329 ⟨24,by decide⟩).lower ∧ (cell12329 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12329 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12329 ⟨25,by decide⟩).lower ∧ (cell12329 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12329 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12329 ⟨26,by decide⟩).lower ∧ (cell12329 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12329 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12329 ⟨27,by decide⟩).lower ∧ (cell12329 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12329 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12329 ⟨28,by decide⟩).lower ∧ (cell12329 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12329 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12329 ⟨29,by decide⟩).lower ∧ (cell12329 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12329 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12329 ⟨30,by decide⟩).lower ∧ (cell12329 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12329 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12329 ⟨31,by decide⟩).lower ∧ (cell12329 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12329 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12329 ⟨32,by decide⟩).lower ∧ (cell12329 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12329 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12329 ⟨33,by decide⟩).lower ∧ (cell12329 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12329 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12329 ⟨34,by decide⟩).lower ∧ (cell12329 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12329 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12329 ⟨35,by decide⟩).lower ∧ (cell12329 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12329 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12329 ⟨36,by decide⟩).lower ∧ (cell12329 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12329 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12329 ⟨37,by decide⟩).lower ∧ (cell12329 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12329 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12329 ⟨38,by decide⟩).lower ∧ (cell12329 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12329 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12329 ⟨39,by decide⟩).lower ∧ (cell12329 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12329 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12329 ⟨40,by decide⟩).lower ∧ (cell12329 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12329 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12329 ⟨41,by decide⟩).lower ∧ (cell12329 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12329 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12329 ⟨42,by decide⟩).lower ∧ (cell12329 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12329 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12329 ⟨43,by decide⟩).lower ∧ (cell12329 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12329 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12329 ⟨44,by decide⟩).lower ∧ (cell12329 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12329 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12329 ⟨45,by decide⟩).lower ∧ (cell12329 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12329 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12329 ⟨46,by decide⟩).lower ∧ (cell12329 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12329 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12329 ⟨47,by decide⟩).lower ∧ (cell12329 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12329 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12329 ⟨48,by decide⟩).lower ∧ (cell12329 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12329 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12329 ⟨49,by decide⟩).lower ∧ (cell12329 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12329 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12329 ⟨50,by decide⟩).lower ∧ (cell12329 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12329 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12329 ⟨51,by decide⟩).lower ∧ (cell12329 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12329 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12329 ⟨52,by decide⟩).lower ∧ (cell12329 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12329 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12329 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12329 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12329,cell12329,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12329 i).lower ∧
    (cell12329 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12329 i).upper ≤ (0.532 : ℝ) ∧
    (cell12329 i).centre ≤ (0.1 : ℝ) ∧ (cell12329 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12329 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12329 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12329

/-! The local source numeric instances at 12329 have no network premises. -/
namespace BstLean.Part264b.N12329
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12329 cell12329)

noncomputable def sourceNumerics12329 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12329 (cell12329 i)
      scalarRow12329.M scalarRow12329.H scalarRow12329.xi := by
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
    energy_allowance := scalarRow12329.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12329]
    centre_nonneg := (scalarRow12329.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12329]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12329
/-! Actual 12330 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12330
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12330 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12330 12330 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12330.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12330 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12330 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12330 := gPlus_lower 12330
end BstLean.Part264b.N12330

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12330
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036347293800 : ℝ) ≤ wn 12330 := by
  have hn : √(12330 : ℝ) ≤ 111.040533139931 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12330 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.040533139931 ≤ 2 / √12330 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259574109 : ℝ) ≤ rhoBar 12330 BstLean.Part154.csC ∧
    rhoBar 12330 BstLean.Part154.csC ≤ 0.000259614012 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036347293800 : ℝ) / (1.295212 * 12330) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12330) := by gcongr
      _ ≤ (0.000259614012 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12330 BstLean.Part154.csC) ≤ 0.001038523448 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12330 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12330 BstLean.Part154.csC) (piBar (rhoBar 12330 BstLean.Part154.csC)) ≤ 0.000198295217 ∧
    cc1 (rhoBar 12330 BstLean.Part154.csC) (piBar (rhoBar 12330 BstLean.Part154.csC)) ≤ 0.000126176505 ∧
    cc2 (rhoBar 12330 BstLean.Part154.csC) ≤ 0.000073246357 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12330 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12330 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12330 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12330 BstLean.Part154.csC * nuR (rhoBar 12330 BstLean.Part154.csC)) ≤ 0.000519244874 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259614012 : ℝ) * 0.001038523448 := by gcongr
      _ ≤ (0.000519244874 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12330 BstLean.Part154.csC) * nuR (rhoBar 12330 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038523448 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12330 BstLean.Part154.csC) * rhoBar 12330 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259614012 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259614012 / 2 + 0.399 * 0.001038523448 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198295217 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519244874 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126176505 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259614012 / 1.414213562 := by gcongr
      _ ≤ (0.000073246357 : ℝ) := by norm_num

end BstLean.Part264b.N12330

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12330
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12330 BstLean.Part154.csC) (piBar (rhoBar 12330 BstLean.Part154.csC)) ≤ 1.69808E-7 := by
  have hr0 : 0 ≤ rhoBar 12330 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12330 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12330 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12330 BstLean.Part154.csC) (piBar (rhoBar 12330 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12330 BstLean.Part154.csC) (piBar (rhoBar 12330 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12330 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198295217 : ℝ) ^ 2 + 0.000126176505 ^ 2 + 3 * 0.000073246357 ^ 2 +
        2 * 0.797885 * 0.000198295217 * 0.000126176505 + 2 * 0.000198295217 * 0.000073246357 +
        4 * 0.797885 * 0.000126176505 * 0.000073246357 := by gcongr
    _ ≤ (1.69808E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12330 BstLean.Part154.csC Θ ≤ 0.002712240319 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12330 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12330 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12330 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12330 BstLean.Part154.csC) (piBar (rhoBar 12330 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12330 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69808E-7 / (0.000259574109 : ℝ) := by gcongr
    _ ≤ 0.002712240319 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12330 BstLean.Part154.csC Θ ≤ 0.003010947071 + 0.000685235312 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12330 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12330 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12330 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259614012 +
        (6863 / 10000) * 0.000259614012 * 12330 * 0.001038523448) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003010947071 + 0.000685235312 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12330 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12330 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12330 0.011 Θ ∧ gammaRatio 12330 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12330 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12330) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12330 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12330 0.011 Θ) :=
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
    badAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12330 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12330 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12330 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12330 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12330 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12330 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12330 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12330 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12330 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12330 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12330 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004110947071 + 0.003397475631 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12330

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12330
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12330 BstLean.Part154.csC) (piBar (rhoBar 12330 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12330 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12330 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12330 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12330 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12330 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12330 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12330 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12330 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12330 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12330 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12330 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12330 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053274571757 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12330) ≤ 0.010754969806 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12330 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010754969806 + 2 * 0.737676 / 12330) := by gcongr
    _ ≤ (0.053274571757 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12330 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12330

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12330
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486333682 : ℝ) ≤ plow 12330 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12330) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053401221778)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423926168) : eMP 12330 0.011 xi bn ≤ 0.001225105797 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12330 : ℝ) * (1 - 0.011))) ≤ 0.000605674113 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001423926168 / (12330 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605674113 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605674113 : ℝ) + 3.141593 * 0.053401221778 / (12330 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225105797 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053401221778)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423926168) : PiBarMP 12330 12 0.011 xi bn ≤ 0.163687482500 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12330 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037734946244 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.428121418414 : ℝ) ≤ √((12330 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.040533139930 : ℝ) ≤ √12330 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12330) ≤ 0.125471374000 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037734946244 + 0.053401221778 * 1.772454 / (2 * (110.428121418414 : ℝ))) * (1 + 0.001225105797) +
        8 / (12330 * 111.040533139930) + 0.125471374000 := by gcongr
    _ ≤ (0.163687482500 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053401221778)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423926168) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284361615483) :
    parallelOracle 12330 0.011 xi bn cd ≤ 0.164711058322 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12330 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12330 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486333682 : ℝ) ≤ plow 12330 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.040533139930 : ℝ) ≤ √12330 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284361615483 : ℝ) / (2 * 0.560486333682 * 111.040533139930)) * 0.163687482500 +
        0.284361615483 ^ 2 / (2 * 0.560486333682 * 111.040533139930) := by gcongr
    _ ≤ (0.164711058322 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053401221778) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423926168)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284361615483) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12330 12330 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486333682 : ℝ) ≤ plow 12330 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.040533139930 : ℝ) ≤ √12330 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12330 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12330 Θ 1.22 ≤ 0.011942490391 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.040533139930 := by gcongr <;> linarith
      _ ≤ (0.011942490391 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12330 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12330 12330 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12330 12330 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12330 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12330 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12330 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12330 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164711058322 + 0.011942490391 + (0.008646 : ℝ) *
        (1 + 2 * (0.284361615483 + 0.011942490391) / (0.560486333682 * 111.040533139930))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12330]

end BstLean.Part264b.N12330

/-! The original eight local profiles supply actual 12330 moment certificates. -/
namespace BstLean.Part264b.N12330
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12330 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053401221778 ∧
    0 ≤ bN 12330 BstLean.Part154.csC (groupTheta g) ∧ bN 12330 BstLean.Part154.csC (groupTheta g) ≤ 0.001423926168 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12330 12330 0.011
      (momentAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12330 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12330 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12330 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231087043726 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12330 0.011
      (momentAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12330 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12330
/-! The actual computed-centre upper energy formula at 12330. -/
namespace BstLean.Part264b.N12330
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12330

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12330
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12330 cell12330)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086653975321
  | 2 => 0.087620149013
  | 3 => 0.088588197593
  | 4 => 0.089560373700
  | 5 => 0.090539369952
  | 6 => 0.091528379992
  | 7 => 0.092531164495
  | 8 => 0.093552122080
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12330 12330 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12330 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12330

/-! Actual upper energy certificates on all 43 source endpoints at 12330. -/
namespace BstLean.Part264b.N12330
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12330 cell12330)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12330 (gMinus 12330) (1 - (cell12330 i).lower) ≤ 1 ∧
    energyUpper 12330 (gMinus 12330) (BstLean.Part211.gPlus 12330)
      (finiteEnergy 12330 12330 0.011) (1 - (cell12330 i).lower) ≤
      (cell12330 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12330) (by norm_num)
        (q := 1 - (cell12330 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12330,cell12330]) (by norm_num [scalarRow12330,cell12330])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12330,cell12330])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12330

/-! Source-cell containment and simple scalar guards at 12330. -/
namespace BstLean.Part264b.N12330
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12330 cell12330)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12330 ⟨10,by decide⟩).lower ∧ (cell12330 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12330 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12330 ⟨11,by decide⟩).lower ∧ (cell12330 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12330 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12330 ⟨12,by decide⟩).lower ∧ (cell12330 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12330 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12330 ⟨13,by decide⟩).lower ∧ (cell12330 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12330 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12330 ⟨14,by decide⟩).lower ∧ (cell12330 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12330 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12330 ⟨15,by decide⟩).lower ∧ (cell12330 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12330 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12330 ⟨16,by decide⟩).lower ∧ (cell12330 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12330 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12330 ⟨17,by decide⟩).lower ∧ (cell12330 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12330 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12330 ⟨18,by decide⟩).lower ∧ (cell12330 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12330 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12330 ⟨19,by decide⟩).lower ∧ (cell12330 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12330 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12330 ⟨20,by decide⟩).lower ∧ (cell12330 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12330 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12330 ⟨21,by decide⟩).lower ∧ (cell12330 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12330 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12330 ⟨22,by decide⟩).lower ∧ (cell12330 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12330 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12330 ⟨23,by decide⟩).lower ∧ (cell12330 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12330 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12330 ⟨24,by decide⟩).lower ∧ (cell12330 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12330 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12330 ⟨25,by decide⟩).lower ∧ (cell12330 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12330 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12330 ⟨26,by decide⟩).lower ∧ (cell12330 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12330 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12330 ⟨27,by decide⟩).lower ∧ (cell12330 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12330 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12330 ⟨28,by decide⟩).lower ∧ (cell12330 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12330 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12330 ⟨29,by decide⟩).lower ∧ (cell12330 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12330 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12330 ⟨30,by decide⟩).lower ∧ (cell12330 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12330 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12330 ⟨31,by decide⟩).lower ∧ (cell12330 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12330 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12330 ⟨32,by decide⟩).lower ∧ (cell12330 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12330 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12330 ⟨33,by decide⟩).lower ∧ (cell12330 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12330 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12330 ⟨34,by decide⟩).lower ∧ (cell12330 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12330 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12330 ⟨35,by decide⟩).lower ∧ (cell12330 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12330 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12330 ⟨36,by decide⟩).lower ∧ (cell12330 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12330 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12330 ⟨37,by decide⟩).lower ∧ (cell12330 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12330 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12330 ⟨38,by decide⟩).lower ∧ (cell12330 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12330 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12330 ⟨39,by decide⟩).lower ∧ (cell12330 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12330 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12330 ⟨40,by decide⟩).lower ∧ (cell12330 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12330 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12330 ⟨41,by decide⟩).lower ∧ (cell12330 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12330 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12330 ⟨42,by decide⟩).lower ∧ (cell12330 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12330 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12330 ⟨43,by decide⟩).lower ∧ (cell12330 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12330 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12330 ⟨44,by decide⟩).lower ∧ (cell12330 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12330 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12330 ⟨45,by decide⟩).lower ∧ (cell12330 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12330 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12330 ⟨46,by decide⟩).lower ∧ (cell12330 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12330 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12330 ⟨47,by decide⟩).lower ∧ (cell12330 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12330 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12330 ⟨48,by decide⟩).lower ∧ (cell12330 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12330 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12330 ⟨49,by decide⟩).lower ∧ (cell12330 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12330 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12330 ⟨50,by decide⟩).lower ∧ (cell12330 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12330 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12330 ⟨51,by decide⟩).lower ∧ (cell12330 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12330 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12330 ⟨52,by decide⟩).lower ∧ (cell12330 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12330 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12330 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12330 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12330,cell12330,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12330 i).lower ∧
    (cell12330 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12330 i).upper ≤ (0.532 : ℝ) ∧
    (cell12330 i).centre ≤ (0.1 : ℝ) ∧ (cell12330 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12330 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12330 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12330

/-! The local source numeric instances at 12330 have no network premises. -/
namespace BstLean.Part264b.N12330
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12330 cell12330)

noncomputable def sourceNumerics12330 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12330 (cell12330 i)
      scalarRow12330.M scalarRow12330.H scalarRow12330.xi := by
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
    energy_allowance := scalarRow12330.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12330]
    centre_nonneg := (scalarRow12330.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12330]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12330
/-! Actual 12331 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12331
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12331 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12331 12331 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12331.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12331 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12331 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12331 := gPlus_lower 12331
end BstLean.Part264b.N12331

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12331
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036345806798 : ℝ) ≤ wn 12331 := by
  have hn : √(12331 : ℝ) ≤ 111.045035908860 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12331 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.045035908860 ≤ 2 / √12331 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259552686 : ℝ) ≤ rhoBar 12331 BstLean.Part154.csC ∧
    rhoBar 12331 BstLean.Part154.csC ≤ 0.000259592958 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036345806798 : ℝ) / (1.295212 * 12331) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12331) := by gcongr
      _ ≤ (0.000259592958 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12331 BstLean.Part154.csC) ≤ 0.001038439221 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12331 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12331 BstLean.Part154.csC) (piBar (rhoBar 12331 BstLean.Part154.csC)) ≤ 0.000198279135 ∧
    cc1 (rhoBar 12331 BstLean.Part154.csC) (piBar (rhoBar 12331 BstLean.Part154.csC)) ≤ 0.000126166272 ∧
    cc2 (rhoBar 12331 BstLean.Part154.csC) ≤ 0.000073240417 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12331 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12331 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12331 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12331 BstLean.Part154.csC * nuR (rhoBar 12331 BstLean.Part154.csC)) ≤ 0.000519202763 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259592958 : ℝ) * 0.001038439221 := by gcongr
      _ ≤ (0.000519202763 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12331 BstLean.Part154.csC) * nuR (rhoBar 12331 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038439221 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12331 BstLean.Part154.csC) * rhoBar 12331 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259592958 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259592958 / 2 + 0.399 * 0.001038439221 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198279135 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519202763 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126166272 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259592958 / 1.414213562 := by gcongr
      _ ≤ (0.000073240417 : ℝ) := by norm_num

end BstLean.Part264b.N12331

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12331
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12331 BstLean.Part154.csC) (piBar (rhoBar 12331 BstLean.Part154.csC)) ≤ 1.69781E-7 := by
  have hr0 : 0 ≤ rhoBar 12331 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12331 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12331 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12331 BstLean.Part154.csC) (piBar (rhoBar 12331 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12331 BstLean.Part154.csC) (piBar (rhoBar 12331 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12331 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198279135 : ℝ) ^ 2 + 0.000126166272 ^ 2 + 3 * 0.000073240417 ^ 2 +
        2 * 0.797885 * 0.000198279135 * 0.000126166272 + 2 * 0.000198279135 * 0.000073240417 +
        4 * 0.797885 * 0.000126166272 * 0.000073240417 := by gcongr
    _ ≤ (1.69781E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12331 BstLean.Part154.csC Θ ≤ 0.002712032892 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12331 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12331 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12331 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12331 BstLean.Part154.csC) (piBar (rhoBar 12331 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12331 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69781E-7 / (0.000259552686 : ℝ) := by gcongr
    _ ≤ 0.002712032892 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12331 BstLean.Part154.csC Θ ≤ 0.003010702873 + 0.000685179741 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12331 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12331 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12331 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259592958 +
        (6863 / 10000) * 0.000259592958 * 12331 * 0.001038439221) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003010702873 + 0.000685179741 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12331 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12331 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12331 0.011 Θ ∧ gammaRatio 12331 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12331 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12331) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12331 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12331 0.011 Θ) :=
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
    badAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12331 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12331 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12331 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12331 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12331 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12331 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12331 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12331 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12331 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12331 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12331 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004110702873 + 0.003397212633 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12331

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12331
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12331 BstLean.Part154.csC) (piBar (rhoBar 12331 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12331 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12331 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12331 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12331 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12331 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12331 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12331 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12331 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12331 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12331 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12331 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12331 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053272387754 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12331) ≤ 0.010754533702 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12331 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010754533702 + 2 * 0.737676 / 12331) := by gcongr
    _ ≤ (0.053272387754 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12331 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12331

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12331
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486381655 : ℝ) ≤ plow 12331 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12331) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400839506)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423817269) : eMP 12331 0.011 xi bn ≤ 0.001225009145 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12331 : ℝ) * (1 - 0.011))) ≤ 0.000605626394 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001423817269 / (12331 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605626394 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605626394 : ℝ) + 3.141593 * 0.053400839506 / (12331 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001225009145 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400839506)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423817269) : PiBarMP 12331 12 0.011 xi bn ≤ 0.163680925145 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12331 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037733503270 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.432599353632 : ℝ) ≤ √((12331 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.045035908859 : ℝ) ≤ √12331 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12331) ≤ 0.125466286257 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037733503270 + 0.053400839506 * 1.772454 / (2 * (110.432599353632 : ℝ))) * (1 + 0.001225009145) +
        8 / (12331 * 111.045035908859) + 0.125466286257 := by gcongr
    _ ≤ (0.163680925145 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400839506)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423817269) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284358604362) :
    parallelOracle 12331 0.011 xi bn cd ≤ 0.164704426678 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12331 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12331 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486381655 : ℝ) ≤ plow 12331 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.045035908859 : ℝ) ≤ √12331 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284358604362 : ℝ) / (2 * 0.560486381655 * 111.045035908859)) * 0.163680925145 +
        0.284358604362 ^ 2 / (2 * 0.560486381655 * 111.045035908859) := by gcongr
    _ ≤ (0.164704426678 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400839506) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423817269)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284358604362) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12331 12331 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486381655 : ℝ) ≤ plow 12331 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.045035908859 : ℝ) ≤ √12331 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12331 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12331 Θ 1.22 ≤ 0.011942006135 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.045035908859 := by gcongr <;> linarith
      _ ≤ (0.011942006135 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12331 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12331 12331 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12331 12331 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12331 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12331 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12331 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12331 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164704426678 + 0.011942006135 + (0.008646 : ℝ) *
        (1 + 2 * (0.284358604362 + 0.011942006135) / (0.560486381655 * 111.045035908859))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12331]

end BstLean.Part264b.N12331

/-! The original eight local profiles supply actual 12331 moment certificates. -/
namespace BstLean.Part264b.N12331
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12331 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053400839506 ∧
    0 ≤ bN 12331 BstLean.Part154.csC (groupTheta g) ∧ bN 12331 BstLean.Part154.csC (groupTheta g) ≤ 0.001423817269 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12331 12331 0.011
      (momentAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12331 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12331 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12331 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231086216608 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12331 0.011
      (momentAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12331 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12331
/-! The actual computed-centre upper energy formula at 12331. -/
namespace BstLean.Part264b.N12331
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12331

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12331
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12331 cell12331)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086650570019
  | 2 => 0.087616669004
  | 3 => 0.088584630125
  | 4 => 0.089556703241
  | 5 => 0.090535577733
  | 6 => 0.091524443488
  | 7 => 0.092527056859
  | 8 => 0.093547811518
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12331 12331 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12331 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12331

/-! Actual upper energy certificates on all 43 source endpoints at 12331. -/
namespace BstLean.Part264b.N12331
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12331 cell12331)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12331 (gMinus 12331) (1 - (cell12331 i).lower) ≤ 1 ∧
    energyUpper 12331 (gMinus 12331) (BstLean.Part211.gPlus 12331)
      (finiteEnergy 12331 12331 0.011) (1 - (cell12331 i).lower) ≤
      (cell12331 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12331) (by norm_num)
        (q := 1 - (cell12331 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12331,cell12331]) (by norm_num [scalarRow12331,cell12331])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12331,cell12331])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12331

/-! Source-cell containment and simple scalar guards at 12331. -/
namespace BstLean.Part264b.N12331
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12331 cell12331)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12331 ⟨10,by decide⟩).lower ∧ (cell12331 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12331 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12331 ⟨11,by decide⟩).lower ∧ (cell12331 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12331 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12331 ⟨12,by decide⟩).lower ∧ (cell12331 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12331 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12331 ⟨13,by decide⟩).lower ∧ (cell12331 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12331 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12331 ⟨14,by decide⟩).lower ∧ (cell12331 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12331 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12331 ⟨15,by decide⟩).lower ∧ (cell12331 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12331 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12331 ⟨16,by decide⟩).lower ∧ (cell12331 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12331 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12331 ⟨17,by decide⟩).lower ∧ (cell12331 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12331 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12331 ⟨18,by decide⟩).lower ∧ (cell12331 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12331 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12331 ⟨19,by decide⟩).lower ∧ (cell12331 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12331 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12331 ⟨20,by decide⟩).lower ∧ (cell12331 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12331 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12331 ⟨21,by decide⟩).lower ∧ (cell12331 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12331 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12331 ⟨22,by decide⟩).lower ∧ (cell12331 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12331 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12331 ⟨23,by decide⟩).lower ∧ (cell12331 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12331 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12331 ⟨24,by decide⟩).lower ∧ (cell12331 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12331 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12331 ⟨25,by decide⟩).lower ∧ (cell12331 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12331 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12331 ⟨26,by decide⟩).lower ∧ (cell12331 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12331 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12331 ⟨27,by decide⟩).lower ∧ (cell12331 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12331 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12331 ⟨28,by decide⟩).lower ∧ (cell12331 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12331 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12331 ⟨29,by decide⟩).lower ∧ (cell12331 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12331 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12331 ⟨30,by decide⟩).lower ∧ (cell12331 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12331 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12331 ⟨31,by decide⟩).lower ∧ (cell12331 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12331 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12331 ⟨32,by decide⟩).lower ∧ (cell12331 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12331 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12331 ⟨33,by decide⟩).lower ∧ (cell12331 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12331 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12331 ⟨34,by decide⟩).lower ∧ (cell12331 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12331 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12331 ⟨35,by decide⟩).lower ∧ (cell12331 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12331 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12331 ⟨36,by decide⟩).lower ∧ (cell12331 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12331 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12331 ⟨37,by decide⟩).lower ∧ (cell12331 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12331 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12331 ⟨38,by decide⟩).lower ∧ (cell12331 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12331 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12331 ⟨39,by decide⟩).lower ∧ (cell12331 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12331 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12331 ⟨40,by decide⟩).lower ∧ (cell12331 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12331 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12331 ⟨41,by decide⟩).lower ∧ (cell12331 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12331 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12331 ⟨42,by decide⟩).lower ∧ (cell12331 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12331 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12331 ⟨43,by decide⟩).lower ∧ (cell12331 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12331 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12331 ⟨44,by decide⟩).lower ∧ (cell12331 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12331 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12331 ⟨45,by decide⟩).lower ∧ (cell12331 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12331 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12331 ⟨46,by decide⟩).lower ∧ (cell12331 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12331 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12331 ⟨47,by decide⟩).lower ∧ (cell12331 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12331 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12331 ⟨48,by decide⟩).lower ∧ (cell12331 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12331 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12331 ⟨49,by decide⟩).lower ∧ (cell12331 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12331 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12331 ⟨50,by decide⟩).lower ∧ (cell12331 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12331 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12331 ⟨51,by decide⟩).lower ∧ (cell12331 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12331 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12331 ⟨52,by decide⟩).lower ∧ (cell12331 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12331 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12331 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12331 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12331,cell12331,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12331 i).lower ∧
    (cell12331 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12331 i).upper ≤ (0.532 : ℝ) ∧
    (cell12331 i).centre ≤ (0.1 : ℝ) ∧ (cell12331 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12331 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12331 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12331

/-! The local source numeric instances at 12331 have no network premises. -/
namespace BstLean.Part264b.N12331
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12331 cell12331)

noncomputable def sourceNumerics12331 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12331 (cell12331 i)
      scalarRow12331.M scalarRow12331.H scalarRow12331.xi := by
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
    energy_allowance := scalarRow12331.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12331]
    centre_nonneg := (scalarRow12331.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12331]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12331
/-! Actual 12332 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12332
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12332 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12332 12332 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12332.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12332 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12332 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12332 := gPlus_lower 12332
end BstLean.Part264b.N12332

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12332
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036344319978 : ℝ) ≤ wn 12332 := by
  have hn : √(12332 : ℝ) ≤ 111.049538495214 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12332 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.049538495214 ≤ 2 / √12332 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259531267 : ℝ) ≤ rhoBar 12332 BstLean.Part154.csC ∧
    rhoBar 12332 BstLean.Part154.csC ≤ 0.000259571908 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036344319978 : ℝ) / (1.295212 * 12332) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12332) := by gcongr
      _ ≤ (0.000259571908 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12332 BstLean.Part154.csC) ≤ 0.001038355010 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12332 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12332 BstLean.Part154.csC) (piBar (rhoBar 12332 BstLean.Part154.csC)) ≤ 0.000198263056 ∧
    cc1 (rhoBar 12332 BstLean.Part154.csC) (piBar (rhoBar 12332 BstLean.Part154.csC)) ≤ 0.000126156041 ∧
    cc2 (rhoBar 12332 BstLean.Part154.csC) ≤ 0.000073234478 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12332 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12332 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12332 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12332 BstLean.Part154.csC * nuR (rhoBar 12332 BstLean.Part154.csC)) ≤ 0.000519160661 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259571908 : ℝ) * 0.001038355010 := by gcongr
      _ ≤ (0.000519160661 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12332 BstLean.Part154.csC) * nuR (rhoBar 12332 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038355010 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12332 BstLean.Part154.csC) * rhoBar 12332 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259571908 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259571908 / 2 + 0.399 * 0.001038355010 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198263056 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519160661 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126156041 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259571908 / 1.414213562 := by gcongr
      _ ≤ (0.000073234478 : ℝ) := by norm_num

end BstLean.Part264b.N12332

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12332
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12332 BstLean.Part154.csC) (piBar (rhoBar 12332 BstLean.Part154.csC)) ≤ 1.69753E-7 := by
  have hr0 : 0 ≤ rhoBar 12332 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12332 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12332 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12332 BstLean.Part154.csC) (piBar (rhoBar 12332 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12332 BstLean.Part154.csC) (piBar (rhoBar 12332 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12332 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198263056 : ℝ) ^ 2 + 0.000126156041 ^ 2 + 3 * 0.000073234478 ^ 2 +
        2 * 0.797885 * 0.000198263056 * 0.000126156041 + 2 * 0.000198263056 * 0.000073234478 +
        4 * 0.797885 * 0.000126156041 * 0.000073234478 := by gcongr
    _ ≤ (1.69753E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12332 BstLean.Part154.csC Θ ≤ 0.002711809414 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12332 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12332 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12332 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12332 BstLean.Part154.csC) (piBar (rhoBar 12332 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12332 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69753E-7 / (0.000259531267 : ℝ) := by gcongr
    _ ≤ 0.002711809414 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12332 BstLean.Part154.csC Θ ≤ 0.003010458728 + 0.000685124181 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12332 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12332 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12332 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259571908 +
        (6863 / 10000) * 0.000259571908 * 12332 * 0.001038355010) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003010458728 + 0.000685124181 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12332 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12332 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12332 0.011 Θ ∧ gammaRatio 12332 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12332 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12332) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12332 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12332 0.011 Θ) :=
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
    badAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12332 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12332 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12332 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12332 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12332 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12332 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12332 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12332 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12332 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12332 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12332 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004110458728 + 0.003396933595 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12332

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12332
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12332 BstLean.Part154.csC) (piBar (rhoBar 12332 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12332 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12332 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12332 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12332 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12332 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12332 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12332 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12332 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12332 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12332 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12332 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12332 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053270204019 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12332) ≤ 0.010754097651 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12332 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010754097651 + 2 * 0.737676 / 12332) := by gcongr
    _ ≤ (0.053270204019 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12332 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12332

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12332
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486429622 : ℝ) ≤ plow 12332 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12332) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400448866)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423699943) : eMP 12332 0.011 xi bn ≤ 0.001224908913 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12332 : ℝ) * (1 - 0.011))) ≤ 0.000605576886 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001423699943 / (12332 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605576886 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605576886 : ℝ) + 3.141593 * 0.053400448866 / (12332 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001224908913 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400448866)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423699943) : PiBarMP 12332 12 0.011 xi bn ≤ 0.163674256348 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12332 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037731948572 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.437077107283 : ℝ) ≤ √((12332 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.049538495213 : ℝ) ≤ √12332 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12332) ≤ 0.125461199133 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037731948572 + 0.053400448866 * 1.772454 / (2 * (110.437077107283 : ℝ))) * (1 + 0.001224908913) +
        8 / (12332 * 111.049538495213) + 0.125461199133 := by gcongr
    _ ≤ (0.163674256348 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400448866)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423699943) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284355575400) :
    parallelOracle 12332 0.011 xi bn cd ≤ 0.164697683240 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12332 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12332 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486429622 : ℝ) ≤ plow 12332 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.049538495213 : ℝ) ≤ √12332 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284355575400 : ℝ) / (2 * 0.560486429622 * 111.049538495213)) * 0.163674256348 +
        0.284355575400 ^ 2 / (2 * 0.560486429622 * 111.049538495213) := by gcongr
    _ ≤ (0.164697683240 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400448866) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423699943)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284355575400) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12332 12332 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486429622 : ℝ) ≤ plow 12332 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.049538495213 : ℝ) ≤ √12332 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12332 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12332 Θ 1.22 ≤ 0.011941521937 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.049538495213 := by gcongr <;> linarith
      _ ≤ (0.011941521937 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12332 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12332 12332 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12332 12332 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12332 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12332 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12332 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12332 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164697683240 + 0.011941521937 + (0.008646 : ℝ) *
        (1 + 2 * (0.284355575400 + 0.011941521937) / (0.560486429622 * 111.049538495213))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12332]

end BstLean.Part264b.N12332

/-! The original eight local profiles supply actual 12332 moment certificates. -/
namespace BstLean.Part264b.N12332
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12332 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053400448866 ∧
    0 ≤ bN 12332 BstLean.Part154.csC (groupTheta g) ∧ bN 12332 BstLean.Part154.csC (groupTheta g) ≤ 0.001423699943 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12332 12332 0.011
      (momentAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12332 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12332 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12332 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231085371381 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12332 0.011
      (momentAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12332 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12332
/-! The actual computed-centre upper energy formula at 12332. -/
namespace BstLean.Part264b.N12332
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12332

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12332
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12332 cell12332)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086647166321
  | 2 => 0.087613190672
  | 3 => 0.088581064421
  | 4 => 0.089553034655
  | 5 => 0.090531787519
  | 6 => 0.091520509149
  | 7 => 0.092522951582
  | 8 => 0.093543503546
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12332 12332 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12332 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12332

/-! Actual upper energy certificates on all 43 source endpoints at 12332. -/
namespace BstLean.Part264b.N12332
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12332 cell12332)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12332 (gMinus 12332) (1 - (cell12332 i).lower) ≤ 1 ∧
    energyUpper 12332 (gMinus 12332) (BstLean.Part211.gPlus 12332)
      (finiteEnergy 12332 12332 0.011) (1 - (cell12332 i).lower) ≤
      (cell12332 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12332) (by norm_num)
        (q := 1 - (cell12332 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12332,cell12332]) (by norm_num [scalarRow12332,cell12332])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12332,cell12332])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12332

/-! Source-cell containment and simple scalar guards at 12332. -/
namespace BstLean.Part264b.N12332
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12332 cell12332)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12332 ⟨10,by decide⟩).lower ∧ (cell12332 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12332 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12332 ⟨11,by decide⟩).lower ∧ (cell12332 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12332 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12332 ⟨12,by decide⟩).lower ∧ (cell12332 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12332 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12332 ⟨13,by decide⟩).lower ∧ (cell12332 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12332 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12332 ⟨14,by decide⟩).lower ∧ (cell12332 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12332 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12332 ⟨15,by decide⟩).lower ∧ (cell12332 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12332 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12332 ⟨16,by decide⟩).lower ∧ (cell12332 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12332 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12332 ⟨17,by decide⟩).lower ∧ (cell12332 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12332 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12332 ⟨18,by decide⟩).lower ∧ (cell12332 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12332 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12332 ⟨19,by decide⟩).lower ∧ (cell12332 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12332 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12332 ⟨20,by decide⟩).lower ∧ (cell12332 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12332 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12332 ⟨21,by decide⟩).lower ∧ (cell12332 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12332 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12332 ⟨22,by decide⟩).lower ∧ (cell12332 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12332 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12332 ⟨23,by decide⟩).lower ∧ (cell12332 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12332 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12332 ⟨24,by decide⟩).lower ∧ (cell12332 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12332 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12332 ⟨25,by decide⟩).lower ∧ (cell12332 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12332 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12332 ⟨26,by decide⟩).lower ∧ (cell12332 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12332 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12332 ⟨27,by decide⟩).lower ∧ (cell12332 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12332 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12332 ⟨28,by decide⟩).lower ∧ (cell12332 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12332 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12332 ⟨29,by decide⟩).lower ∧ (cell12332 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12332 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12332 ⟨30,by decide⟩).lower ∧ (cell12332 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12332 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12332 ⟨31,by decide⟩).lower ∧ (cell12332 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12332 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12332 ⟨32,by decide⟩).lower ∧ (cell12332 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12332 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12332 ⟨33,by decide⟩).lower ∧ (cell12332 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12332 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12332 ⟨34,by decide⟩).lower ∧ (cell12332 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12332 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12332 ⟨35,by decide⟩).lower ∧ (cell12332 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12332 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12332 ⟨36,by decide⟩).lower ∧ (cell12332 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12332 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12332 ⟨37,by decide⟩).lower ∧ (cell12332 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12332 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12332 ⟨38,by decide⟩).lower ∧ (cell12332 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12332 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12332 ⟨39,by decide⟩).lower ∧ (cell12332 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12332 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12332 ⟨40,by decide⟩).lower ∧ (cell12332 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12332 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12332 ⟨41,by decide⟩).lower ∧ (cell12332 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12332 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12332 ⟨42,by decide⟩).lower ∧ (cell12332 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12332 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12332 ⟨43,by decide⟩).lower ∧ (cell12332 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12332 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12332 ⟨44,by decide⟩).lower ∧ (cell12332 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12332 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12332 ⟨45,by decide⟩).lower ∧ (cell12332 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12332 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12332 ⟨46,by decide⟩).lower ∧ (cell12332 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12332 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12332 ⟨47,by decide⟩).lower ∧ (cell12332 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12332 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12332 ⟨48,by decide⟩).lower ∧ (cell12332 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12332 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12332 ⟨49,by decide⟩).lower ∧ (cell12332 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12332 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12332 ⟨50,by decide⟩).lower ∧ (cell12332 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12332 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12332 ⟨51,by decide⟩).lower ∧ (cell12332 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12332 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12332 ⟨52,by decide⟩).lower ∧ (cell12332 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12332 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12332 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12332 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12332,cell12332,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12332 i).lower ∧
    (cell12332 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12332 i).upper ≤ (0.532 : ℝ) ∧
    (cell12332 i).centre ≤ (0.1 : ℝ) ∧ (cell12332 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12332 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12332 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12332

/-! The local source numeric instances at 12332 have no network premises. -/
namespace BstLean.Part264b.N12332
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12332 cell12332)

noncomputable def sourceNumerics12332 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12332 (cell12332 i)
      scalarRow12332.M scalarRow12332.H scalarRow12332.xi := by
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
    energy_allowance := scalarRow12332.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12332]
    centre_nonneg := (scalarRow12332.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12332]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12332
/-! Actual 12333 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12333
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12333 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12333 12333 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12333.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12333 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12333 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12333 := gPlus_lower 12333
end BstLean.Part264b.N12333

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12333
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036342833341 : ℝ) ≤ wn 12333 := by
  have hn : √(12333 : ℝ) ≤ 111.054040899015 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12333 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.054040899015 ≤ 2 / √12333 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259509851 : ℝ) ≤ rhoBar 12333 BstLean.Part154.csC ∧
    rhoBar 12333 BstLean.Part154.csC ≤ 0.000259550861 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036342833341 : ℝ) / (1.295212 * 12333) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12333) := by gcongr
      _ ≤ (0.000259550861 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12333 BstLean.Part154.csC) ≤ 0.001038270811 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12333 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12333 BstLean.Part154.csC) (piBar (rhoBar 12333 BstLean.Part154.csC)) ≤ 0.000198246979 ∧
    cc1 (rhoBar 12333 BstLean.Part154.csC) (piBar (rhoBar 12333 BstLean.Part154.csC)) ≤ 0.000126145812 ∧
    cc2 (rhoBar 12333 BstLean.Part154.csC) ≤ 0.000073228540 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12333 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12333 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12333 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12333 BstLean.Part154.csC * nuR (rhoBar 12333 BstLean.Part154.csC)) ≤ 0.000519118564 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259550861 : ℝ) * 0.001038270811 := by gcongr
      _ ≤ (0.000519118564 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12333 BstLean.Part154.csC) * nuR (rhoBar 12333 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038270811 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12333 BstLean.Part154.csC) * rhoBar 12333 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259550861 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259550861 / 2 + 0.399 * 0.001038270811 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198246979 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519118564 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126145812 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259550861 / 1.414213562 := by gcongr
      _ ≤ (0.000073228540 : ℝ) := by norm_num

end BstLean.Part264b.N12333

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12333
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12333 BstLean.Part154.csC) (piBar (rhoBar 12333 BstLean.Part154.csC)) ≤ 1.69726E-7 := by
  have hr0 : 0 ≤ rhoBar 12333 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12333 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12333 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12333 BstLean.Part154.csC) (piBar (rhoBar 12333 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12333 BstLean.Part154.csC) (piBar (rhoBar 12333 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12333 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198246979 : ℝ) ^ 2 + 0.000126145812 ^ 2 + 3 * 0.000073228540 ^ 2 +
        2 * 0.797885 * 0.000198246979 * 0.000126145812 + 2 * 0.000198246979 * 0.000073228540 +
        4 * 0.797885 * 0.000126145812 * 0.000073228540 := by gcongr
    _ ≤ (1.69726E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12333 BstLean.Part154.csC Θ ≤ 0.002711601845 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12333 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12333 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12333 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12333 BstLean.Part154.csC) (piBar (rhoBar 12333 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12333 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69726E-7 / (0.000259509851 : ℝ) := by gcongr
    _ ≤ 0.002711601845 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12333 BstLean.Part154.csC Θ ≤ 0.003010214612 + 0.000685068629 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12333 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12333 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12333 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259550861 +
        (6863 / 10000) * 0.000259550861 * 12333 * 0.001038270811) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003010214612 + 0.000685068629 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12333 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12333 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12333 0.011 Θ ∧ gammaRatio 12333 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12333 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12333) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12333 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12333 0.011 Θ) :=
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
    badAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12333 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12333 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12333 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12333 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12333 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12333 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12333 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12333 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12333 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12333 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12333 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004110214612 + 0.003396670474 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12333

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12333
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12333 BstLean.Part154.csC) (piBar (rhoBar 12333 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12333 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12333 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12333 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12333 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12333 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12333 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12333 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12333 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12333 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12333 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12333 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12333 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053268020556 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12333) ≤ 0.010753661654 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12333 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010753661654 + 2 * 0.737676 / 12333) := by gcongr
    _ ≤ (0.053268020556 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12333 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12333

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12333
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486477580 : ℝ) ≤ plow 12333 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12333) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400066611)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423590969) : eMP 12333 0.011 xi bn ≤ 0.001224812245 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12333 : ℝ) * (1 - 0.011))) ≤ 0.000605529159 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001423590969 / (12333 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605529159 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605529159 : ℝ) + 3.141593 * 0.053400066611 / (12333 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001224812245 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400066611)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423590969) : PiBarMP 12333 12 0.011 xi bn ≤ 0.163667699127 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12333 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037730504490 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.441554679386 : ℝ) ≤ √((12333 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.054040899014 : ℝ) ≤ √12333 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12333) ≤ 0.125456112628 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037730504490 + 0.053400066611 * 1.772454 / (2 * (110.441554679386 : ℝ))) * (1 + 0.001224812245) +
        8 / (12333 * 111.054040899014) + 0.125456112628 := by gcongr
    _ ≤ (0.163667699127 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400066611)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423590969) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284352564849) :
    parallelOracle 12333 0.011 xi bn cd ≤ 0.164691051750 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12333 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12333 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486477580 : ℝ) ≤ plow 12333 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.054040899014 : ℝ) ≤ √12333 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284352564849 : ℝ) / (2 * 0.560486477580 * 111.054040899014)) * 0.163667699127 +
        0.284352564849 ^ 2 / (2 * 0.560486477580 * 111.054040899014) := by gcongr
    _ ≤ (0.164691051750 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053400066611) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423590969)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284352564849) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12333 12333 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486477580 : ℝ) ≤ plow 12333 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.054040899014 : ℝ) ≤ √12333 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12333 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12333 Θ 1.22 ≤ 0.011941037799 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.054040899014 := by gcongr <;> linarith
      _ ≤ (0.011941037799 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12333 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12333 12333 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12333 12333 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12333 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12333 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12333 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12333 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164691051750 + 0.011941037799 + (0.008646 : ℝ) *
        (1 + 2 * (0.284352564849 + 0.011941037799) / (0.560486477580 * 111.054040899014))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12333]

end BstLean.Part264b.N12333

/-! The original eight local profiles supply actual 12333 moment certificates. -/
namespace BstLean.Part264b.N12333
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12333 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053400066611 ∧
    0 ≤ bN 12333 BstLean.Part154.csC (groupTheta g) ∧ bN 12333 BstLean.Part154.csC (groupTheta g) ≤ 0.001423590969 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12333 12333 0.011
      (momentAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12333 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12333 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12333 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231084544293 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12333 0.011
      (momentAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12333 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12333
/-! The actual computed-centre upper energy formula at 12333. -/
namespace BstLean.Part264b.N12333
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12333

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12333
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12333 cell12333)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086643764225
  | 2 => 0.087609714013
  | 3 => 0.088577500480
  | 4 => 0.089549367941
  | 5 => 0.090527999309
  | 6 => 0.091516576975
  | 7 => 0.092518848662
  | 8 => 0.093539198161
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12333 12333 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12333 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12333

/-! Actual upper energy certificates on all 43 source endpoints at 12333. -/
namespace BstLean.Part264b.N12333
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12333 cell12333)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12333 (gMinus 12333) (1 - (cell12333 i).lower) ≤ 1 ∧
    energyUpper 12333 (gMinus 12333) (BstLean.Part211.gPlus 12333)
      (finiteEnergy 12333 12333 0.011) (1 - (cell12333 i).lower) ≤
      (cell12333 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12333) (by norm_num)
        (q := 1 - (cell12333 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12333,cell12333]) (by norm_num [scalarRow12333,cell12333])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12333,cell12333])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12333

/-! Source-cell containment and simple scalar guards at 12333. -/
namespace BstLean.Part264b.N12333
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12333 cell12333)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12333 ⟨10,by decide⟩).lower ∧ (cell12333 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12333 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12333 ⟨11,by decide⟩).lower ∧ (cell12333 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12333 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12333 ⟨12,by decide⟩).lower ∧ (cell12333 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12333 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12333 ⟨13,by decide⟩).lower ∧ (cell12333 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12333 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12333 ⟨14,by decide⟩).lower ∧ (cell12333 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12333 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12333 ⟨15,by decide⟩).lower ∧ (cell12333 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12333 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12333 ⟨16,by decide⟩).lower ∧ (cell12333 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12333 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12333 ⟨17,by decide⟩).lower ∧ (cell12333 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12333 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12333 ⟨18,by decide⟩).lower ∧ (cell12333 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12333 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12333 ⟨19,by decide⟩).lower ∧ (cell12333 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12333 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12333 ⟨20,by decide⟩).lower ∧ (cell12333 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12333 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12333 ⟨21,by decide⟩).lower ∧ (cell12333 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12333 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12333 ⟨22,by decide⟩).lower ∧ (cell12333 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12333 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12333 ⟨23,by decide⟩).lower ∧ (cell12333 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12333 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12333 ⟨24,by decide⟩).lower ∧ (cell12333 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12333 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12333 ⟨25,by decide⟩).lower ∧ (cell12333 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12333 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12333 ⟨26,by decide⟩).lower ∧ (cell12333 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12333 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12333 ⟨27,by decide⟩).lower ∧ (cell12333 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12333 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12333 ⟨28,by decide⟩).lower ∧ (cell12333 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12333 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12333 ⟨29,by decide⟩).lower ∧ (cell12333 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12333 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12333 ⟨30,by decide⟩).lower ∧ (cell12333 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12333 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12333 ⟨31,by decide⟩).lower ∧ (cell12333 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12333 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12333 ⟨32,by decide⟩).lower ∧ (cell12333 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12333 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12333 ⟨33,by decide⟩).lower ∧ (cell12333 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12333 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12333 ⟨34,by decide⟩).lower ∧ (cell12333 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12333 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12333 ⟨35,by decide⟩).lower ∧ (cell12333 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12333 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12333 ⟨36,by decide⟩).lower ∧ (cell12333 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12333 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12333 ⟨37,by decide⟩).lower ∧ (cell12333 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12333 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12333 ⟨38,by decide⟩).lower ∧ (cell12333 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12333 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12333 ⟨39,by decide⟩).lower ∧ (cell12333 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12333 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12333 ⟨40,by decide⟩).lower ∧ (cell12333 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12333 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12333 ⟨41,by decide⟩).lower ∧ (cell12333 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12333 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12333 ⟨42,by decide⟩).lower ∧ (cell12333 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12333 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12333 ⟨43,by decide⟩).lower ∧ (cell12333 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12333 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12333 ⟨44,by decide⟩).lower ∧ (cell12333 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12333 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12333 ⟨45,by decide⟩).lower ∧ (cell12333 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12333 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12333 ⟨46,by decide⟩).lower ∧ (cell12333 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12333 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12333 ⟨47,by decide⟩).lower ∧ (cell12333 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12333 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12333 ⟨48,by decide⟩).lower ∧ (cell12333 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12333 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12333 ⟨49,by decide⟩).lower ∧ (cell12333 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12333 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12333 ⟨50,by decide⟩).lower ∧ (cell12333 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12333 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12333 ⟨51,by decide⟩).lower ∧ (cell12333 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12333 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12333 ⟨52,by decide⟩).lower ∧ (cell12333 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12333 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12333 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12333 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12333,cell12333,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12333 i).lower ∧
    (cell12333 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12333 i).upper ≤ (0.532 : ℝ) ∧
    (cell12333 i).centre ≤ (0.1 : ℝ) ∧ (cell12333 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12333 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12333 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12333

/-! The local source numeric instances at 12333 have no network premises. -/
namespace BstLean.Part264b.N12333
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12333 cell12333)

noncomputable def sourceNumerics12333 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12333 (cell12333 i)
      scalarRow12333.M scalarRow12333.H scalarRow12333.xi := by
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
    energy_allowance := scalarRow12333.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12333]
    centre_nonneg := (scalarRow12333.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12333]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12333
/-! Actual 12334 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12334
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12334 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12334 12334 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12334.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12334 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12334 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12334 := gPlus_lower 12334
end BstLean.Part264b.N12334

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12334
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036341346885 : ℝ) ≤ wn 12334 := by
  have hn : √(12334 : ℝ) ≤ 111.058543120285 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12334 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.058543120285 ≤ 2 / √12334 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259488438 : ℝ) ≤ rhoBar 12334 BstLean.Part154.csC ∧
    rhoBar 12334 BstLean.Part154.csC ≤ 0.000259529817 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036341346885 : ℝ) / (1.295212 * 12334) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12334) := by gcongr
      _ ≤ (0.000259529817 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12334 BstLean.Part154.csC) ≤ 0.001038186624 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12334 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12334 BstLean.Part154.csC) (piBar (rhoBar 12334 BstLean.Part154.csC)) ≤ 0.000198230905 ∧
    cc1 (rhoBar 12334 BstLean.Part154.csC) (piBar (rhoBar 12334 BstLean.Part154.csC)) ≤ 0.000126135583 ∧
    cc2 (rhoBar 12334 BstLean.Part154.csC) ≤ 0.000073222603 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12334 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12334 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12334 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12334 BstLean.Part154.csC * nuR (rhoBar 12334 BstLean.Part154.csC)) ≤ 0.000519076473 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259529817 : ℝ) * 0.001038186624 := by gcongr
      _ ≤ (0.000519076473 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12334 BstLean.Part154.csC) * nuR (rhoBar 12334 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038186624 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12334 BstLean.Part154.csC) * rhoBar 12334 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259529817 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259529817 / 2 + 0.399 * 0.001038186624 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198230905 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519076473 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126135583 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259529817 / 1.414213562 := by gcongr
      _ ≤ (0.000073222603 : ℝ) := by norm_num

end BstLean.Part264b.N12334

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12334
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12334 BstLean.Part154.csC) (piBar (rhoBar 12334 BstLean.Part154.csC)) ≤ 1.69698E-7 := by
  have hr0 : 0 ≤ rhoBar 12334 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12334 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12334 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12334 BstLean.Part154.csC) (piBar (rhoBar 12334 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12334 BstLean.Part154.csC) (piBar (rhoBar 12334 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12334 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198230905 : ℝ) ^ 2 + 0.000126135583 ^ 2 + 3 * 0.000073222603 ^ 2 +
        2 * 0.797885 * 0.000198230905 * 0.000126135583 + 2 * 0.000198230905 * 0.000073222603 +
        4 * 0.797885 * 0.000126135583 * 0.000073222603 := by gcongr
    _ ≤ (1.69698E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12334 BstLean.Part154.csC Θ ≤ 0.002711378231 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12334 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12334 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12334 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12334 BstLean.Part154.csC) (piBar (rhoBar 12334 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12334 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69698E-7 / (0.000259488438 : ℝ) := by gcongr
    _ ≤ 0.002711378231 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12334 BstLean.Part154.csC Θ ≤ 0.003009970527 + 0.000685013084 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12334 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12334 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12334 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259529817 +
        (6863 / 10000) * 0.000259529817 * 12334 * 0.001038186624) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003009970527 + 0.000685013084 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12334 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12334 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12334 0.011 Θ ∧ gammaRatio 12334 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12334 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12334) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12334 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12334 0.011 Θ) :=
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
    badAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12334 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12334 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12334 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12334 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12334 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12334 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12334 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12334 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12334 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12334 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12334 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004109970527 + 0.003396391315 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12334

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12334
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12334 BstLean.Part154.csC) (piBar (rhoBar 12334 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12334 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12334 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12334 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12334 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12334 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12334 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12334 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12334 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12334 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12334 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12334 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12334 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053265837355 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12334) ≤ 0.010753225709 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12334 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010753225709 + 2 * 0.737676 / 12334) := by gcongr
    _ ≤ (0.053265837355 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12334 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12334

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12334
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486525531 : ℝ) ≤ plow 12334 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12334) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053399675968)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423473572) : eMP 12334 0.011 xi bn ≤ 0.001224711999 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12334 : ℝ) * (1 - 0.011))) ≤ 0.000605479644 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001423473572 / (12334 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605479644 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605479644 : ℝ) + 3.141593 * 0.053399675968 / (12334 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001224711999 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053399675968)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423473572) : PiBarMP 12334 12 0.011 xi bn ≤ 0.163661030505 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12334 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037728948727 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.446032069966 : ℝ) ≤ √((12334 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.058543120284 : ℝ) ≤ √12334 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12334) ≤ 0.125451026741 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037728948727 + 0.053399675968 * 1.772454 / (2 * (110.446032069966 : ℝ))) * (1 + 0.001224711999) +
        8 / (12334 * 111.058543120284) + 0.125451026741 := by gcongr
    _ ≤ (0.163661030505 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053399675968)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423473572) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284349536408) :
    parallelOracle 12334 0.011 xi bn cd ≤ 0.164684308508 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12334 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12334 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486525531 : ℝ) ≤ plow 12334 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.058543120284 : ℝ) ≤ √12334 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284349536408 : ℝ) / (2 * 0.560486525531 * 111.058543120284)) * 0.163661030505 +
        0.284349536408 ^ 2 / (2 * 0.560486525531 * 111.058543120284) := by gcongr
    _ ≤ (0.164684308508 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053399675968) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423473572)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284349536408) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12334 12334 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486525531 : ℝ) ≤ plow 12334 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.058543120284 : ℝ) ≤ √12334 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12334 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12334 Θ 1.22 ≤ 0.011940553719 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.058543120284 := by gcongr <;> linarith
      _ ≤ (0.011940553719 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12334 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12334 12334 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12334 12334 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12334 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12334 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12334 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12334 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164684308508 + 0.011940553719 + (0.008646 : ℝ) *
        (1 + 2 * (0.284349536408 + 0.011940553719) / (0.560486525531 * 111.058543120284))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12334]

end BstLean.Part264b.N12334

/-! The original eight local profiles supply actual 12334 moment certificates. -/
namespace BstLean.Part264b.N12334
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12334 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053399675968 ∧
    0 ≤ bN 12334 BstLean.Part154.csC (groupTheta g) ∧ bN 12334 BstLean.Part154.csC (groupTheta g) ≤ 0.001423473572 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12334 12334 0.011
      (momentAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12334 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12334 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12334 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231083699053 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12334 0.011
      (momentAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12334 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12334
/-! The actual computed-centre upper energy formula at 12334. -/
namespace BstLean.Part264b.N12334
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12334

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12334
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12334 cell12334)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086640363728
  | 2 => 0.087606239026
  | 3 => 0.088573938299
  | 4 => 0.089545703095
  | 5 => 0.090524213100
  | 6 => 0.091512646962
  | 7 => 0.092514748095
  | 8 => 0.093534895360
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12334 12334 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12334 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12334

/-! Actual upper energy certificates on all 43 source endpoints at 12334. -/
namespace BstLean.Part264b.N12334
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12334 cell12334)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12334 (gMinus 12334) (1 - (cell12334 i).lower) ≤ 1 ∧
    energyUpper 12334 (gMinus 12334) (BstLean.Part211.gPlus 12334)
      (finiteEnergy 12334 12334 0.011) (1 - (cell12334 i).lower) ≤
      (cell12334 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12334) (by norm_num)
        (q := 1 - (cell12334 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12334,cell12334]) (by norm_num [scalarRow12334,cell12334])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12334,cell12334])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12334

/-! Source-cell containment and simple scalar guards at 12334. -/
namespace BstLean.Part264b.N12334
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12334 cell12334)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12334 ⟨10,by decide⟩).lower ∧ (cell12334 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12334 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12334 ⟨11,by decide⟩).lower ∧ (cell12334 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12334 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12334 ⟨12,by decide⟩).lower ∧ (cell12334 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12334 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12334 ⟨13,by decide⟩).lower ∧ (cell12334 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12334 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12334 ⟨14,by decide⟩).lower ∧ (cell12334 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12334 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12334 ⟨15,by decide⟩).lower ∧ (cell12334 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12334 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12334 ⟨16,by decide⟩).lower ∧ (cell12334 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12334 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12334 ⟨17,by decide⟩).lower ∧ (cell12334 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12334 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12334 ⟨18,by decide⟩).lower ∧ (cell12334 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12334 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12334 ⟨19,by decide⟩).lower ∧ (cell12334 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12334 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12334 ⟨20,by decide⟩).lower ∧ (cell12334 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12334 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12334 ⟨21,by decide⟩).lower ∧ (cell12334 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12334 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12334 ⟨22,by decide⟩).lower ∧ (cell12334 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12334 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12334 ⟨23,by decide⟩).lower ∧ (cell12334 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12334 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12334 ⟨24,by decide⟩).lower ∧ (cell12334 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12334 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12334 ⟨25,by decide⟩).lower ∧ (cell12334 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12334 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12334 ⟨26,by decide⟩).lower ∧ (cell12334 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12334 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12334 ⟨27,by decide⟩).lower ∧ (cell12334 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12334 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12334 ⟨28,by decide⟩).lower ∧ (cell12334 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12334 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12334 ⟨29,by decide⟩).lower ∧ (cell12334 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12334 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12334 ⟨30,by decide⟩).lower ∧ (cell12334 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12334 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12334 ⟨31,by decide⟩).lower ∧ (cell12334 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12334 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12334 ⟨32,by decide⟩).lower ∧ (cell12334 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12334 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12334 ⟨33,by decide⟩).lower ∧ (cell12334 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12334 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12334 ⟨34,by decide⟩).lower ∧ (cell12334 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12334 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12334 ⟨35,by decide⟩).lower ∧ (cell12334 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12334 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12334 ⟨36,by decide⟩).lower ∧ (cell12334 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12334 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12334 ⟨37,by decide⟩).lower ∧ (cell12334 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12334 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12334 ⟨38,by decide⟩).lower ∧ (cell12334 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12334 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12334 ⟨39,by decide⟩).lower ∧ (cell12334 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12334 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12334 ⟨40,by decide⟩).lower ∧ (cell12334 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12334 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12334 ⟨41,by decide⟩).lower ∧ (cell12334 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12334 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12334 ⟨42,by decide⟩).lower ∧ (cell12334 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12334 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12334 ⟨43,by decide⟩).lower ∧ (cell12334 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12334 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12334 ⟨44,by decide⟩).lower ∧ (cell12334 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12334 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12334 ⟨45,by decide⟩).lower ∧ (cell12334 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12334 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12334 ⟨46,by decide⟩).lower ∧ (cell12334 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12334 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12334 ⟨47,by decide⟩).lower ∧ (cell12334 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12334 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12334 ⟨48,by decide⟩).lower ∧ (cell12334 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12334 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12334 ⟨49,by decide⟩).lower ∧ (cell12334 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12334 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12334 ⟨50,by decide⟩).lower ∧ (cell12334 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12334 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12334 ⟨51,by decide⟩).lower ∧ (cell12334 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12334 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12334 ⟨52,by decide⟩).lower ∧ (cell12334 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12334 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12334 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12334 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12334,cell12334,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12334 i).lower ∧
    (cell12334 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12334 i).upper ≤ (0.532 : ℝ) ∧
    (cell12334 i).centre ≤ (0.1 : ℝ) ∧ (cell12334 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12334 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12334 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12334

/-! The local source numeric instances at 12334 have no network premises. -/
namespace BstLean.Part264b.N12334
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12334 cell12334)

noncomputable def sourceNumerics12334 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12334 (cell12334 i)
      scalarRow12334.M scalarRow12334.H scalarRow12334.xi := by
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
    energy_allowance := scalarRow12334.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12334]
    centre_nonneg := (scalarRow12334.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12334]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12334
/-! Actual 12335 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12335
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12335 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12335 12335 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12335.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12335 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12335 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12335 := gPlus_lower 12335
end BstLean.Part264b.N12335

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12335
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036339860610 : ℝ) ≤ wn 12335 := by
  have hn : √(12335 : ℝ) ≤ 111.063045159045 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12335 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.063045159045 ≤ 2 / √12335 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259467030 : ℝ) ≤ rhoBar 12335 BstLean.Part154.csC ∧
    rhoBar 12335 BstLean.Part154.csC ≤ 0.000259508777 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036339860610 : ℝ) / (1.295212 * 12335) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12335) := by gcongr
      _ ≤ (0.000259508777 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12335 BstLean.Part154.csC) ≤ 0.001038102453 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12335 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12335 BstLean.Part154.csC) (piBar (rhoBar 12335 BstLean.Part154.csC)) ≤ 0.000198214834 ∧
    cc1 (rhoBar 12335 BstLean.Part154.csC) (piBar (rhoBar 12335 BstLean.Part154.csC)) ≤ 0.000126125357 ∧
    cc2 (rhoBar 12335 BstLean.Part154.csC) ≤ 0.000073216667 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12335 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12335 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12335 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12335 BstLean.Part154.csC * nuR (rhoBar 12335 BstLean.Part154.csC)) ≤ 0.000519034390 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259508777 : ℝ) * 0.001038102453 := by gcongr
      _ ≤ (0.000519034390 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12335 BstLean.Part154.csC) * nuR (rhoBar 12335 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038102453 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12335 BstLean.Part154.csC) * rhoBar 12335 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259508777 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259508777 / 2 + 0.399 * 0.001038102453 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198214834 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000519034390 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126125357 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259508777 / 1.414213562 := by gcongr
      _ ≤ (0.000073216667 : ℝ) := by norm_num

end BstLean.Part264b.N12335

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12335
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12335 BstLean.Part154.csC) (piBar (rhoBar 12335 BstLean.Part154.csC)) ≤ 1.69671E-7 := by
  have hr0 : 0 ≤ rhoBar 12335 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12335 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12335 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12335 BstLean.Part154.csC) (piBar (rhoBar 12335 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12335 BstLean.Part154.csC) (piBar (rhoBar 12335 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12335 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198214834 : ℝ) ^ 2 + 0.000126125357 ^ 2 + 3 * 0.000073216667 ^ 2 +
        2 * 0.797885 * 0.000198214834 * 0.000126125357 + 2 * 0.000198214834 * 0.000073216667 +
        4 * 0.797885 * 0.000126125357 * 0.000073216667 := by gcongr
    _ ≤ (1.69671E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12335 BstLean.Part154.csC Θ ≤ 0.002711170508 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12335 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12335 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12335 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12335 BstLean.Part154.csC) (piBar (rhoBar 12335 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12335 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69671E-7 / (0.000259467030 : ℝ) := by gcongr
    _ ≤ 0.002711170508 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12335 BstLean.Part154.csC Θ ≤ 0.003009726495 + 0.000684957550 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12335 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12335 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12335 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259508777 +
        (6863 / 10000) * 0.000259508777 * 12335 * 0.001038102453) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003009726495 + 0.000684957550 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12335 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12335 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12335 0.011 Θ ∧ gammaRatio 12335 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12335 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12335) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12335 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12335 0.011 Θ) :=
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
    badAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12335 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12335 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12335 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12335 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12335 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12335 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12335 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12335 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12335 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12335 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12335 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004109726495 + 0.003396128058 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12335

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12335
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12335 BstLean.Part154.csC) (piBar (rhoBar 12335 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12335 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12335 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12335 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12335 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12335 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12335 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12335 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12335 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12335 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12335 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12335 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12335 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053263654427 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12335) ≤ 0.010752789818 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12335 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010752789818 + 2 * 0.737676 / 12335) := by gcongr
    _ ≤ (0.053263654427 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12335 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12335

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12335
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486573473 : ℝ) ≤ plow 12335 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12335) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053399293726)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423364517) : eMP 12335 0.011 xi bn ≤ 0.001224615314 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12335 : ℝ) * (1 - 0.011))) ≤ 0.000605431908 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001423364517 / (12335 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605431908 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605431908 : ℝ) + 3.141593 * 0.053399293726 / (12335 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001224615314 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053399293726)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423364517) : PiBarMP 12335 12 0.011 xi bn ≤ 0.163654473336 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12335 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037727503456 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.450509279043 : ℝ) ≤ √((12335 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.063045159044 : ℝ) ≤ √12335 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12335) ≤ 0.125445941473 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037727503456 + 0.053399293726 * 1.772454 / (2 * (110.450509279043 : ℝ))) * (1 + 0.001224615314) +
        8 / (12335 * 111.063045159044) + 0.125445941473 := by gcongr
    _ ≤ (0.163654473336 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053399293726)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423364517) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284346526415) :
    parallelOracle 12335 0.011 xi bn cd ≤ 0.164677677089 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12335 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12335 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486573473 : ℝ) ≤ plow 12335 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.063045159044 : ℝ) ≤ √12335 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284346526415 : ℝ) / (2 * 0.560486573473 * 111.063045159044)) * 0.163654473336 +
        0.284346526415 ^ 2 / (2 * 0.560486573473 * 111.063045159044) := by gcongr
    _ ≤ (0.164677677089 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053399293726) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423364517)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284346526415) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12335 12335 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486573473 : ℝ) ≤ plow 12335 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.063045159044 : ℝ) ≤ √12335 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12335 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12335 Θ 1.22 ≤ 0.011940069698 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.063045159044 := by gcongr <;> linarith
      _ ≤ (0.011940069698 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12335 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12335 12335 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12335 12335 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12335 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12335 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12335 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12335 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164677677089 + 0.011940069698 + (0.008646 : ℝ) *
        (1 + 2 * (0.284346526415 + 0.011940069698) / (0.560486573473 * 111.063045159044))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12335]

end BstLean.Part264b.N12335

/-! The original eight local profiles supply actual 12335 moment certificates. -/
namespace BstLean.Part264b.N12335
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12335 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053399293726 ∧
    0 ≤ bN 12335 BstLean.Part154.csC (groupTheta g) ∧ bN 12335 BstLean.Part154.csC (groupTheta g) ≤ 0.001423364517 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12335 12335 0.011
      (momentAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12335 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12335 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12335 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231082871988 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12335 0.011
      (momentAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12335 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12335
/-! The actual computed-centre upper energy formula at 12335. -/
namespace BstLean.Part264b.N12335
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12335

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12335
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12335 cell12335)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086636964830
  | 2 => 0.087602765709
  | 3 => 0.088570377877
  | 4 => 0.089542040117
  | 5 => 0.090520428890
  | 6 => 0.091508719107
  | 7 => 0.092510649880
  | 8 => 0.093530595140
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12335 12335 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12335 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12335

/-! Actual upper energy certificates on all 43 source endpoints at 12335. -/
namespace BstLean.Part264b.N12335
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12335 cell12335)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12335 (gMinus 12335) (1 - (cell12335 i).lower) ≤ 1 ∧
    energyUpper 12335 (gMinus 12335) (BstLean.Part211.gPlus 12335)
      (finiteEnergy 12335 12335 0.011) (1 - (cell12335 i).lower) ≤
      (cell12335 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12335) (by norm_num)
        (q := 1 - (cell12335 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12335,cell12335]) (by norm_num [scalarRow12335,cell12335])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12335,cell12335])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12335

/-! Source-cell containment and simple scalar guards at 12335. -/
namespace BstLean.Part264b.N12335
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12335 cell12335)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12335 ⟨10,by decide⟩).lower ∧ (cell12335 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12335 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12335 ⟨11,by decide⟩).lower ∧ (cell12335 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12335 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12335 ⟨12,by decide⟩).lower ∧ (cell12335 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12335 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12335 ⟨13,by decide⟩).lower ∧ (cell12335 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12335 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12335 ⟨14,by decide⟩).lower ∧ (cell12335 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12335 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12335 ⟨15,by decide⟩).lower ∧ (cell12335 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12335 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12335 ⟨16,by decide⟩).lower ∧ (cell12335 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12335 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12335 ⟨17,by decide⟩).lower ∧ (cell12335 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12335 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12335 ⟨18,by decide⟩).lower ∧ (cell12335 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12335 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12335 ⟨19,by decide⟩).lower ∧ (cell12335 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12335 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12335 ⟨20,by decide⟩).lower ∧ (cell12335 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12335 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12335 ⟨21,by decide⟩).lower ∧ (cell12335 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12335 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12335 ⟨22,by decide⟩).lower ∧ (cell12335 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12335 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12335 ⟨23,by decide⟩).lower ∧ (cell12335 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12335 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12335 ⟨24,by decide⟩).lower ∧ (cell12335 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12335 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12335 ⟨25,by decide⟩).lower ∧ (cell12335 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12335 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12335 ⟨26,by decide⟩).lower ∧ (cell12335 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12335 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12335 ⟨27,by decide⟩).lower ∧ (cell12335 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12335 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12335 ⟨28,by decide⟩).lower ∧ (cell12335 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12335 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12335 ⟨29,by decide⟩).lower ∧ (cell12335 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12335 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12335 ⟨30,by decide⟩).lower ∧ (cell12335 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12335 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12335 ⟨31,by decide⟩).lower ∧ (cell12335 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12335 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12335 ⟨32,by decide⟩).lower ∧ (cell12335 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12335 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12335 ⟨33,by decide⟩).lower ∧ (cell12335 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12335 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12335 ⟨34,by decide⟩).lower ∧ (cell12335 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12335 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12335 ⟨35,by decide⟩).lower ∧ (cell12335 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12335 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12335 ⟨36,by decide⟩).lower ∧ (cell12335 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12335 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12335 ⟨37,by decide⟩).lower ∧ (cell12335 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12335 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12335 ⟨38,by decide⟩).lower ∧ (cell12335 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12335 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12335 ⟨39,by decide⟩).lower ∧ (cell12335 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12335 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12335 ⟨40,by decide⟩).lower ∧ (cell12335 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12335 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12335 ⟨41,by decide⟩).lower ∧ (cell12335 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12335 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12335 ⟨42,by decide⟩).lower ∧ (cell12335 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12335 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12335 ⟨43,by decide⟩).lower ∧ (cell12335 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12335 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12335 ⟨44,by decide⟩).lower ∧ (cell12335 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12335 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12335 ⟨45,by decide⟩).lower ∧ (cell12335 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12335 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12335 ⟨46,by decide⟩).lower ∧ (cell12335 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12335 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12335 ⟨47,by decide⟩).lower ∧ (cell12335 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12335 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12335 ⟨48,by decide⟩).lower ∧ (cell12335 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12335 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12335 ⟨49,by decide⟩).lower ∧ (cell12335 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12335 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12335 ⟨50,by decide⟩).lower ∧ (cell12335 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12335 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12335 ⟨51,by decide⟩).lower ∧ (cell12335 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12335 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12335 ⟨52,by decide⟩).lower ∧ (cell12335 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12335 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12335 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12335 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12335,cell12335,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12335 i).lower ∧
    (cell12335 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12335 i).upper ≤ (0.532 : ℝ) ∧
    (cell12335 i).centre ≤ (0.1 : ℝ) ∧ (cell12335 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12335 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12335 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12335

/-! The local source numeric instances at 12335 have no network premises. -/
namespace BstLean.Part264b.N12335
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12335 cell12335)

noncomputable def sourceNumerics12335 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12335 (cell12335 i)
      scalarRow12335.M scalarRow12335.H scalarRow12335.xi := by
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
    energy_allowance := scalarRow12335.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12335]
    centre_nonneg := (scalarRow12335.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12335]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12335
/-! Actual 12336 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12336
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12336 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12336 12336 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12336.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12336 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12336 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12336 := gPlus_lower 12336
end BstLean.Part264b.N12336

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12336
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036338374518 : ℝ) ≤ wn 12336 := by
  have hn : √(12336 : ℝ) ≤ 111.067547015319 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12336 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.067547015319 ≤ 2 / √12336 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259445624 : ℝ) ≤ rhoBar 12336 BstLean.Part154.csC ∧
    rhoBar 12336 BstLean.Part154.csC ≤ 0.000259487740 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036338374518 : ℝ) / (1.295212 * 12336) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12336) := by gcongr
      _ ≤ (0.000259487740 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12336 BstLean.Part154.csC) ≤ 0.001038018294 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12336 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12336 BstLean.Part154.csC) (piBar (rhoBar 12336 BstLean.Part154.csC)) ≤ 0.000198198765 ∧
    cc1 (rhoBar 12336 BstLean.Part154.csC) (piBar (rhoBar 12336 BstLean.Part154.csC)) ≤ 0.000126115133 ∧
    cc2 (rhoBar 12336 BstLean.Part154.csC) ≤ 0.000073210731 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12336 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12336 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12336 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12336 BstLean.Part154.csC * nuR (rhoBar 12336 BstLean.Part154.csC)) ≤ 0.000518992314 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259487740 : ℝ) * 0.001038018294 := by gcongr
      _ ≤ (0.000518992314 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12336 BstLean.Part154.csC) * nuR (rhoBar 12336 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001038018294 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12336 BstLean.Part154.csC) * rhoBar 12336 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259487740 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259487740 / 2 + 0.399 * 0.001038018294 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198198765 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518992314 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126115133 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259487740 / 1.414213562 := by gcongr
      _ ≤ (0.000073210731 : ℝ) := by norm_num

end BstLean.Part264b.N12336

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12336
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12336 BstLean.Part154.csC) (piBar (rhoBar 12336 BstLean.Part154.csC)) ≤ 1.69643E-7 := by
  have hr0 : 0 ≤ rhoBar 12336 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12336 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12336 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12336 BstLean.Part154.csC) (piBar (rhoBar 12336 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12336 BstLean.Part154.csC) (piBar (rhoBar 12336 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12336 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198198765 : ℝ) ^ 2 + 0.000126115133 ^ 2 + 3 * 0.000073210731 ^ 2 +
        2 * 0.797885 * 0.000198198765 * 0.000126115133 + 2 * 0.000198198765 * 0.000073210731 +
        4 * 0.797885 * 0.000126115133 * 0.000073210731 := by gcongr
    _ ≤ (1.69643E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12336 BstLean.Part154.csC Θ ≤ 0.002710946749 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12336 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12336 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12336 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12336 BstLean.Part154.csC) (piBar (rhoBar 12336 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12336 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69643E-7 / (0.000259445624 : ℝ) := by gcongr
    _ ≤ 0.002710946749 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12336 BstLean.Part154.csC Θ ≤ 0.003009482493 + 0.000684902025 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12336 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12336 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12336 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259487740 +
        (6863 / 10000) * 0.000259487740 * 12336 * 0.001038018294) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003009482493 + 0.000684902025 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12336 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12336 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12336 0.011 Θ ∧ gammaRatio 12336 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12336 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12336) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12336 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12336 0.011 Θ) :=
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
    badAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12336 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12336 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12336 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12336 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12336 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12336 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12336 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12336 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12336 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12336 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12336 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004109482493 + 0.003395848774 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12336

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12336
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12336 BstLean.Part154.csC) (piBar (rhoBar 12336 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12336 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12336 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12336 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12336 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12336 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12336 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12336 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12336 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12336 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12336 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12336 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12336 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053261471761 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12336) ≤ 0.010752353979 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12336 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010752353979 + 2 * 0.737676 / 12336) := by gcongr
    _ ≤ (0.053261471761 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12336 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12336

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12336
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486621408 : ℝ) ≤ plow 12336 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12336) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398903100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423247044) : eMP 12336 0.011 xi bn ≤ 0.001224515052 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12336 : ℝ) * (1 - 0.011))) ≤ 0.000605382385 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001423247044 / (12336 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605382385 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605382385 : ℝ) + 3.141593 * 0.053398903100 / (12336 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001224515052 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398903100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423247044) : PiBarMP 12336 12 0.011 xi bn ≤ 0.163647804824 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12336 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037725946563 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.454986306639 : ℝ) ≤ √((12336 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.067547015318 : ℝ) ≤ √12336 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12336) ≤ 0.125440856823 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037725946563 + 0.053398903100 * 1.772454 / (2 * (110.454986306639 : ℝ))) * (1 + 0.001224515052) +
        8 / (12336 * 111.067547015318) + 0.125440856823 := by gcongr
    _ ≤ (0.163647804824 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398903100)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423247044) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284343498540) :
    parallelOracle 12336 0.011 xi bn cd ≤ 0.164670933977 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12336 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12336 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486621408 : ℝ) ≤ plow 12336 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.067547015318 : ℝ) ≤ √12336 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284343498540 : ℝ) / (2 * 0.560486621408 * 111.067547015318)) * 0.163647804824 +
        0.284343498540 ^ 2 / (2 * 0.560486621408 * 111.067547015318) := by gcongr
    _ ≤ (0.164670933977 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398903100) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423247044)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284343498540) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12336 12336 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486621408 : ℝ) ≤ plow 12336 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.067547015318 : ℝ) ≤ √12336 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12336 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12336 Θ 1.22 ≤ 0.011939585736 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.067547015318 := by gcongr <;> linarith
      _ ≤ (0.011939585736 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12336 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12336 12336 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12336 12336 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12336 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12336 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12336 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12336 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164670933977 + 0.011939585736 + (0.008646 : ℝ) *
        (1 + 2 * (0.284343498540 + 0.011939585736) / (0.560486621408 * 111.067547015318))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12336]

end BstLean.Part264b.N12336

/-! The original eight local profiles supply actual 12336 moment certificates. -/
namespace BstLean.Part264b.N12336
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12336 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053398903100 ∧
    0 ≤ bN 12336 BstLean.Part154.csC (groupTheta g) ∧ bN 12336 BstLean.Part154.csC (groupTheta g) ≤ 0.001423247044 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12336 12336 0.011
      (momentAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12336 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12336 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12336 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231082026779 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12336 0.011
      (momentAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12336 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12336
/-! The actual computed-centre upper energy formula at 12336. -/
namespace BstLean.Part264b.N12336
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12336

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12336
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12336 cell12336)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086633567529
  | 2 => 0.087599294060
  | 3 => 0.088566819211
  | 4 => 0.089538379004
  | 5 => 0.090516646676
  | 6 => 0.091504793409
  | 7 => 0.092506554012
  | 8 => 0.093526297498
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12336 12336 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12336 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12336

/-! Actual upper energy certificates on all 43 source endpoints at 12336. -/
namespace BstLean.Part264b.N12336
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12336 cell12336)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12336 (gMinus 12336) (1 - (cell12336 i).lower) ≤ 1 ∧
    energyUpper 12336 (gMinus 12336) (BstLean.Part211.gPlus 12336)
      (finiteEnergy 12336 12336 0.011) (1 - (cell12336 i).lower) ≤
      (cell12336 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12336) (by norm_num)
        (q := 1 - (cell12336 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12336,cell12336]) (by norm_num [scalarRow12336,cell12336])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12336,cell12336])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12336

/-! Source-cell containment and simple scalar guards at 12336. -/
namespace BstLean.Part264b.N12336
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12336 cell12336)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12336 ⟨10,by decide⟩).lower ∧ (cell12336 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12336 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12336 ⟨11,by decide⟩).lower ∧ (cell12336 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12336 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12336 ⟨12,by decide⟩).lower ∧ (cell12336 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12336 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12336 ⟨13,by decide⟩).lower ∧ (cell12336 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12336 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12336 ⟨14,by decide⟩).lower ∧ (cell12336 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12336 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12336 ⟨15,by decide⟩).lower ∧ (cell12336 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12336 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12336 ⟨16,by decide⟩).lower ∧ (cell12336 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12336 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12336 ⟨17,by decide⟩).lower ∧ (cell12336 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12336 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12336 ⟨18,by decide⟩).lower ∧ (cell12336 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12336 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12336 ⟨19,by decide⟩).lower ∧ (cell12336 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12336 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12336 ⟨20,by decide⟩).lower ∧ (cell12336 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12336 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12336 ⟨21,by decide⟩).lower ∧ (cell12336 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12336 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12336 ⟨22,by decide⟩).lower ∧ (cell12336 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12336 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12336 ⟨23,by decide⟩).lower ∧ (cell12336 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12336 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12336 ⟨24,by decide⟩).lower ∧ (cell12336 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12336 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12336 ⟨25,by decide⟩).lower ∧ (cell12336 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12336 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12336 ⟨26,by decide⟩).lower ∧ (cell12336 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12336 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12336 ⟨27,by decide⟩).lower ∧ (cell12336 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12336 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12336 ⟨28,by decide⟩).lower ∧ (cell12336 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12336 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12336 ⟨29,by decide⟩).lower ∧ (cell12336 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12336 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12336 ⟨30,by decide⟩).lower ∧ (cell12336 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12336 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12336 ⟨31,by decide⟩).lower ∧ (cell12336 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12336 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12336 ⟨32,by decide⟩).lower ∧ (cell12336 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12336 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12336 ⟨33,by decide⟩).lower ∧ (cell12336 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12336 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12336 ⟨34,by decide⟩).lower ∧ (cell12336 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12336 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12336 ⟨35,by decide⟩).lower ∧ (cell12336 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12336 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12336 ⟨36,by decide⟩).lower ∧ (cell12336 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12336 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12336 ⟨37,by decide⟩).lower ∧ (cell12336 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12336 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12336 ⟨38,by decide⟩).lower ∧ (cell12336 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12336 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12336 ⟨39,by decide⟩).lower ∧ (cell12336 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12336 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12336 ⟨40,by decide⟩).lower ∧ (cell12336 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12336 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12336 ⟨41,by decide⟩).lower ∧ (cell12336 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12336 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12336 ⟨42,by decide⟩).lower ∧ (cell12336 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12336 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12336 ⟨43,by decide⟩).lower ∧ (cell12336 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12336 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12336 ⟨44,by decide⟩).lower ∧ (cell12336 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12336 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12336 ⟨45,by decide⟩).lower ∧ (cell12336 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12336 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12336 ⟨46,by decide⟩).lower ∧ (cell12336 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12336 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12336 ⟨47,by decide⟩).lower ∧ (cell12336 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12336 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12336 ⟨48,by decide⟩).lower ∧ (cell12336 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12336 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12336 ⟨49,by decide⟩).lower ∧ (cell12336 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12336 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12336 ⟨50,by decide⟩).lower ∧ (cell12336 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12336 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12336 ⟨51,by decide⟩).lower ∧ (cell12336 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12336 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12336 ⟨52,by decide⟩).lower ∧ (cell12336 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12336 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12336 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12336 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12336,cell12336,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12336 i).lower ∧
    (cell12336 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12336 i).upper ≤ (0.532 : ℝ) ∧
    (cell12336 i).centre ≤ (0.1 : ℝ) ∧ (cell12336 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12336 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12336 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12336

/-! The local source numeric instances at 12336 have no network premises. -/
namespace BstLean.Part264b.N12336
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12336 cell12336)

noncomputable def sourceNumerics12336 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12336 (cell12336 i)
      scalarRow12336.M scalarRow12336.H scalarRow12336.xi := by
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
    energy_allowance := scalarRow12336.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12336]
    centre_nonneg := (scalarRow12336.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12336]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12336
/-! Actual 12337 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12337
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12337 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12337 12337 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12337.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12337 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12337 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12337 := gPlus_lower 12337
end BstLean.Part264b.N12337

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12337
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036336888607 : ℝ) ≤ wn 12337 := by
  have hn : √(12337 : ℝ) ≤ 111.072048689128 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12337 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.072048689128 ≤ 2 / √12337 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259424222 : ℝ) ≤ rhoBar 12337 BstLean.Part154.csC ∧
    rhoBar 12337 BstLean.Part154.csC ≤ 0.000259466707 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036336888607 : ℝ) / (1.295212 * 12337) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12337) := by gcongr
      _ ≤ (0.000259466707 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12337 BstLean.Part154.csC) ≤ 0.001037934151 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12337 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12337 BstLean.Part154.csC) (piBar (rhoBar 12337 BstLean.Part154.csC)) ≤ 0.000198182699 ∧
    cc1 (rhoBar 12337 BstLean.Part154.csC) (piBar (rhoBar 12337 BstLean.Part154.csC)) ≤ 0.000126104910 ∧
    cc2 (rhoBar 12337 BstLean.Part154.csC) ≤ 0.000073204797 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12337 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12337 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12337 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12337 BstLean.Part154.csC * nuR (rhoBar 12337 BstLean.Part154.csC)) ≤ 0.000518950245 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259466707 : ℝ) * 0.001037934151 := by gcongr
      _ ≤ (0.000518950245 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12337 BstLean.Part154.csC) * nuR (rhoBar 12337 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037934151 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12337 BstLean.Part154.csC) * rhoBar 12337 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259466707 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259466707 / 2 + 0.399 * 0.001037934151 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198182699 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518950245 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126104910 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259466707 / 1.414213562 := by gcongr
      _ ≤ (0.000073204797 : ℝ) := by norm_num

end BstLean.Part264b.N12337

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12337
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12337 BstLean.Part154.csC) (piBar (rhoBar 12337 BstLean.Part154.csC)) ≤ 1.69616E-7 := by
  have hr0 : 0 ≤ rhoBar 12337 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12337 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12337 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12337 BstLean.Part154.csC) (piBar (rhoBar 12337 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12337 BstLean.Part154.csC) (piBar (rhoBar 12337 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12337 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198182699 : ℝ) ^ 2 + 0.000126104910 ^ 2 + 3 * 0.000073204797 ^ 2 +
        2 * 0.797885 * 0.000198182699 * 0.000126104910 + 2 * 0.000198182699 * 0.000073204797 +
        4 * 0.797885 * 0.000126104910 * 0.000073204797 := by gcongr
    _ ≤ (1.69616E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12337 BstLean.Part154.csC Θ ≤ 0.002710738893 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12337 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12337 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12337 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12337 BstLean.Part154.csC) (piBar (rhoBar 12337 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12337 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69616E-7 / (0.000259424222 : ℝ) := by gcongr
    _ ≤ 0.002710738893 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12337 BstLean.Part154.csC Θ ≤ 0.003009238544 + 0.000684846509 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12337 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12337 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12337 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259466707 +
        (6863 / 10000) * 0.000259466707 * 12337 * 0.001037934151) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003009238544 + 0.000684846509 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12337 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12337 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12337 0.011 Θ ∧ gammaRatio 12337 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12337 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12337) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12337 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12337 0.011 Θ) :=
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
    badAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12337 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12337 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12337 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12337 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12337 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12337 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12337 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12337 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12337 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12337 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12337 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004109238544 + 0.003395585402 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12337

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12337
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12337 BstLean.Part154.csC) (piBar (rhoBar 12337 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12337 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12337 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12337 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12337 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12337 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12337 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12337 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12337 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12337 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12337 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12337 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12337 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053259289367 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12337) ≤ 0.010751918194 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12337 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010751918194 + 2 * 0.737676 / 12337) := by gcongr
    _ ≤ (0.053259289367 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12337 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12337

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12337
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486669336 : ℝ) ≤ plow 12337 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12337) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398520881)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423137919) : eMP 12337 0.011 xi bn ≤ 0.001224418352 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12337 : ℝ) * (1 - 0.011))) ≤ 0.000605334641 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001423137919 / (12337 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605334641 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605334641 : ℝ) + 3.141593 * 0.053398520881 / (12337 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001224418352 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398520881)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423137919) : PiBarMP 12337 12 0.011 xi bn ≤ 0.163641247852 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12337 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037724500249 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.459463152778 : ℝ) ≤ √((12337 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.072048689127 : ℝ) ≤ √12337 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12337) ≤ 0.125435772791 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037724500249 + 0.053398520881 * 1.772454 / (2 * (110.459463152778 : ℝ))) * (1 + 0.001224418352) +
        8 / (12337 * 111.072048689127) + 0.125435772791 := by gcongr
    _ ≤ (0.163641247852 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398520881)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423137919) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284340489124) :
    parallelOracle 12337 0.011 xi bn cd ≤ 0.164664302776 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12337 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12337 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486669336 : ℝ) ≤ plow 12337 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.072048689127 : ℝ) ≤ √12337 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284340489124 : ℝ) / (2 * 0.560486669336 * 111.072048689127)) * 0.163641247852 +
        0.284340489124 ^ 2 / (2 * 0.560486669336 * 111.072048689127) := by gcongr
    _ ≤ (0.164664302776 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398520881) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423137919)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284340489124) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12337 12337 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486669336 : ℝ) ≤ plow 12337 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.072048689127 : ℝ) ≤ √12337 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12337 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12337 Θ 1.22 ≤ 0.011939101833 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.072048689127 := by gcongr <;> linarith
      _ ≤ (0.011939101833 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12337 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12337 12337 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12337 12337 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12337 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12337 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12337 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12337 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164664302776 + 0.011939101833 + (0.008646 : ℝ) *
        (1 + 2 * (0.284340489124 + 0.011939101833) / (0.560486669336 * 111.072048689127))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12337]

end BstLean.Part264b.N12337

/-! The original eight local profiles supply actual 12337 moment certificates. -/
namespace BstLean.Part264b.N12337
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12337 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053398520881 ∧
    0 ≤ bN 12337 BstLean.Part154.csC (groupTheta g) ∧ bN 12337 BstLean.Part154.csC (groupTheta g) ≤ 0.001423137919 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12337 12337 0.011
      (momentAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12337 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12337 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12337 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231081199757 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12337 0.011
      (momentAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12337 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12337
/-! The actual computed-centre upper energy formula at 12337. -/
namespace BstLean.Part264b.N12337
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12337

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12337
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12337 cell12337)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086630171822
  | 2 => 0.087595824078
  | 3 => 0.088563262300
  | 4 => 0.089534719753
  | 5 => 0.090512866457
  | 6 => 0.091500869864
  | 7 => 0.092502460490
  | 8 => 0.093522002430
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12337 12337 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12337 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12337

/-! Actual upper energy certificates on all 43 source endpoints at 12337. -/
namespace BstLean.Part264b.N12337
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12337 cell12337)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12337 (gMinus 12337) (1 - (cell12337 i).lower) ≤ 1 ∧
    energyUpper 12337 (gMinus 12337) (BstLean.Part211.gPlus 12337)
      (finiteEnergy 12337 12337 0.011) (1 - (cell12337 i).lower) ≤
      (cell12337 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12337) (by norm_num)
        (q := 1 - (cell12337 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12337,cell12337]) (by norm_num [scalarRow12337,cell12337])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12337,cell12337])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12337

/-! Source-cell containment and simple scalar guards at 12337. -/
namespace BstLean.Part264b.N12337
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12337 cell12337)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12337 ⟨10,by decide⟩).lower ∧ (cell12337 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12337 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12337 ⟨11,by decide⟩).lower ∧ (cell12337 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12337 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12337 ⟨12,by decide⟩).lower ∧ (cell12337 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12337 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12337 ⟨13,by decide⟩).lower ∧ (cell12337 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12337 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12337 ⟨14,by decide⟩).lower ∧ (cell12337 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12337 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12337 ⟨15,by decide⟩).lower ∧ (cell12337 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12337 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12337 ⟨16,by decide⟩).lower ∧ (cell12337 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12337 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12337 ⟨17,by decide⟩).lower ∧ (cell12337 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12337 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12337 ⟨18,by decide⟩).lower ∧ (cell12337 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12337 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12337 ⟨19,by decide⟩).lower ∧ (cell12337 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12337 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12337 ⟨20,by decide⟩).lower ∧ (cell12337 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12337 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12337 ⟨21,by decide⟩).lower ∧ (cell12337 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12337 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12337 ⟨22,by decide⟩).lower ∧ (cell12337 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12337 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12337 ⟨23,by decide⟩).lower ∧ (cell12337 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12337 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12337 ⟨24,by decide⟩).lower ∧ (cell12337 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12337 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12337 ⟨25,by decide⟩).lower ∧ (cell12337 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12337 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12337 ⟨26,by decide⟩).lower ∧ (cell12337 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12337 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12337 ⟨27,by decide⟩).lower ∧ (cell12337 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12337 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12337 ⟨28,by decide⟩).lower ∧ (cell12337 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12337 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12337 ⟨29,by decide⟩).lower ∧ (cell12337 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12337 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12337 ⟨30,by decide⟩).lower ∧ (cell12337 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12337 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12337 ⟨31,by decide⟩).lower ∧ (cell12337 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12337 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12337 ⟨32,by decide⟩).lower ∧ (cell12337 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12337 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12337 ⟨33,by decide⟩).lower ∧ (cell12337 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12337 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12337 ⟨34,by decide⟩).lower ∧ (cell12337 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12337 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12337 ⟨35,by decide⟩).lower ∧ (cell12337 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12337 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12337 ⟨36,by decide⟩).lower ∧ (cell12337 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12337 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12337 ⟨37,by decide⟩).lower ∧ (cell12337 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12337 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12337 ⟨38,by decide⟩).lower ∧ (cell12337 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12337 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12337 ⟨39,by decide⟩).lower ∧ (cell12337 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12337 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12337 ⟨40,by decide⟩).lower ∧ (cell12337 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12337 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12337 ⟨41,by decide⟩).lower ∧ (cell12337 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12337 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12337 ⟨42,by decide⟩).lower ∧ (cell12337 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12337 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12337 ⟨43,by decide⟩).lower ∧ (cell12337 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12337 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12337 ⟨44,by decide⟩).lower ∧ (cell12337 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12337 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12337 ⟨45,by decide⟩).lower ∧ (cell12337 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12337 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12337 ⟨46,by decide⟩).lower ∧ (cell12337 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12337 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12337 ⟨47,by decide⟩).lower ∧ (cell12337 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12337 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12337 ⟨48,by decide⟩).lower ∧ (cell12337 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12337 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12337 ⟨49,by decide⟩).lower ∧ (cell12337 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12337 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12337 ⟨50,by decide⟩).lower ∧ (cell12337 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12337 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12337 ⟨51,by decide⟩).lower ∧ (cell12337 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12337 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12337 ⟨52,by decide⟩).lower ∧ (cell12337 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12337 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12337 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12337 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12337,cell12337,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12337 i).lower ∧
    (cell12337 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12337 i).upper ≤ (0.532 : ℝ) ∧
    (cell12337 i).centre ≤ (0.1 : ℝ) ∧ (cell12337 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12337 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12337 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12337

/-! The local source numeric instances at 12337 have no network premises. -/
namespace BstLean.Part264b.N12337
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12337 cell12337)

noncomputable def sourceNumerics12337 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12337 (cell12337 i)
      scalarRow12337.M scalarRow12337.H scalarRow12337.xi := by
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
    energy_allowance := scalarRow12337.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12337]
    centre_nonneg := (scalarRow12337.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12337]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12337
/-! Actual 12338 scalar aliases and the unchanged imported parallel allowance. -/
