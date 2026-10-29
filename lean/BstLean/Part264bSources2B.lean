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
namespace BstLean.Part264b.N12288
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12288 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12288 12288 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12288.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12288 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12288 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12288 := gPlus_lower 12288
end BstLean.Part264b.N12288

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12288
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036409912657 : ℝ) ≤ wn 12288 := by
  have hn : √(12288 : ℝ) ≤ 110.851251684409 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12288 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.851251684409 ≤ 2 / √12288 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260477063 : ℝ) ≤ rhoBar 12288 BstLean.Part154.csC ∧
    rhoBar 12288 BstLean.Part154.csC ≤ 0.000260501364 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036409912657 : ℝ) / (1.295212 * 12288) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12288) := by gcongr
      _ ≤ (0.000260501364 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12288 BstLean.Part154.csC) ≤ 0.001042073317 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12288 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12288 BstLean.Part154.csC) (piBar (rhoBar 12288 BstLean.Part154.csC)) ≤ 0.000198973016 ∧
    cc1 (rhoBar 12288 BstLean.Part154.csC) (piBar (rhoBar 12288 BstLean.Part154.csC)) ≤ 0.000126607786 ∧
    cc2 (rhoBar 12288 BstLean.Part154.csC) ≤ 0.000073496711 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12288 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12288 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12288 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12288 BstLean.Part154.csC * nuR (rhoBar 12288 BstLean.Part154.csC)) ≤ 0.000521019693 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260501364 : ℝ) * 0.001042073317 := by gcongr
      _ ≤ (0.000521019693 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12288 BstLean.Part154.csC) * nuR (rhoBar 12288 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042073317 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12288 BstLean.Part154.csC) * rhoBar 12288 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260501364 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260501364 / 2 + 0.399 * 0.001042073317 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198973016 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521019693 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126607786 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260501364 / 1.414213562 := by gcongr
      _ ≤ (0.000073496711 : ℝ) := by norm_num

end BstLean.Part264b.N12288

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12288
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12288 BstLean.Part154.csC) (piBar (rhoBar 12288 BstLean.Part154.csC)) ≤ 1.70971E-7 := by
  have hr0 : 0 ≤ rhoBar 12288 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12288 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12288 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12288 BstLean.Part154.csC) (piBar (rhoBar 12288 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12288 BstLean.Part154.csC) (piBar (rhoBar 12288 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12288 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198973016 : ℝ) ^ 2 + 0.000126607786 ^ 2 + 3 * 0.000073496711 ^ 2 +
        2 * 0.797885 * 0.000198973016 * 0.000126607786 + 2 * 0.000198973016 * 0.000073496711 +
        4 * 0.797885 * 0.000126607786 * 0.000073496711 := by gcongr
    _ ≤ (1.70971E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12288 BstLean.Part154.csC Θ ≤ 0.002721349732 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12288 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12288 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12288 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12288 BstLean.Part154.csC) (piBar (rhoBar 12288 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12288 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70971E-7 / (0.000260477063 : ℝ) := by gcongr
    _ ≤ 0.002721349732 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12288 BstLean.Part154.csC Θ ≤ 0.003021239050 + 0.000687577423 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12288 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12288 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12288 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260501364 +
        (6863 / 10000) * 0.000260501364 * 12288 * 0.001042073317) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003021239050 + 0.000687577423 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12288 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12288 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12288 0.011 Θ ∧ gammaRatio 12288 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12288 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12288) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12288 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12288 0.011 Θ) :=
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
    badAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12288 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12288 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12288 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12288 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12288 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12288 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12288 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12288 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12288 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12288 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12288 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004121239050 + 0.003408927155 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12288

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12288
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12288 BstLean.Part154.csC) (piBar (rhoBar 12288 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12288 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12288 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12288 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12288 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12288 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12288 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12288 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12288 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12288 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12288 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12288 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12288 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053366542144 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12288) ≤ 0.010773334202 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12288 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010773334202 + 2 * 0.737676 / 12288) := by gcongr
    _ ≤ (0.053366542144 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12288 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12288

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12288
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484311726 : ℝ) ≤ plow 12288 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12288) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417525807)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428708610) : eMP 12288 0.011 xi bn ≤ 0.001229261445 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12288 : ℝ) * (1 - 0.011))) ≤ 0.000607726318 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001428708610 / (12288 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607726318 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607726318 : ℝ) + 3.141593 * 0.053417525807 / (12288 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001229261445 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417525807)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428708610) : PiBarMP 12288 12 0.011 xi bn ≤ 0.163966174281 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12288 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037798261998 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.239883889634 : ℝ) ≤ √((12288 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.851251684408 : ℝ) ≤ √12288 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12288) ≤ 0.125685619703 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037798261998 + 0.053417525807 * 1.772454 / (2 * (110.239883889634 : ℝ))) * (1 + 0.001229261445) +
        8 / (12288 * 110.851251684408) + 0.125685619703 := by gcongr
    _ ≤ (0.163966174281 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417525807)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428708610) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284488859992) :
    parallelOracle 12288 0.011 xi bn cd ≤ 0.164992889763 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12288 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12288 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484311726 : ℝ) ≤ plow 12288 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.851251684408 : ℝ) ≤ √12288 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284488859992 : ℝ) / (2 * 0.560484311726 * 110.851251684408)) * 0.163966174281 +
        0.284488859992 ^ 2 / (2 * 0.560484311726 * 110.851251684408) := by gcongr
    _ ≤ (0.164992889763 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417525807) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428708610)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284488859992) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12288 12288 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484311726 : ℝ) ≤ plow 12288 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.851251684408 : ℝ) ≤ √12288 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12288 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12288 Θ 1.22 ≤ 0.011962882511 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.851251684408 := by gcongr <;> linarith
      _ ≤ (0.011962882511 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12288 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12288 12288 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12288 12288 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12288 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12288 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12288 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12288 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164992889763 + 0.011962882511 + (0.008646 : ℝ) *
        (1 + 2 * (0.284488859992 + 0.011962882511) / (0.560484311726 * 110.851251684408))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12288]

end BstLean.Part264b.N12288

/-! The original eight local profiles supply actual 12288 moment certificates. -/
namespace BstLean.Part264b.N12288
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12288 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053417525807 ∧
    0 ≤ bN 12288 BstLean.Part154.csC (groupTheta g) ∧ bN 12288 BstLean.Part154.csC (groupTheta g) ≤ 0.001428708610 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12288 12288 0.011
      (momentAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12288 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12288 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12288 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231122317848 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12288 0.011
      (momentAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12288 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12288
/-! The actual computed-centre upper energy formula at 12288. -/
namespace BstLean.Part264b.N12288
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12288

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12288
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12288 cell12288)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086798469828
  | 2 => 0.087767847605
  | 3 => 0.088739651308
  | 4 => 0.089716253185
  | 5 => 0.090700485306
  | 6 => 0.091695702826
  | 7 => 0.092705852312
  | 8 => 0.093735545032
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12288 12288 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12288 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12288

/-! Actual upper energy certificates on all 43 source endpoints at 12288. -/
namespace BstLean.Part264b.N12288
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12288 cell12288)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12288 (gMinus 12288) (1 - (cell12288 i).lower) ≤ 1 ∧
    energyUpper 12288 (gMinus 12288) (BstLean.Part211.gPlus 12288)
      (finiteEnergy 12288 12288 0.011) (1 - (cell12288 i).lower) ≤
      (cell12288 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12288) (by norm_num)
        (q := 1 - (cell12288 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12288,cell12288]) (by norm_num [scalarRow12288,cell12288])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12288,cell12288])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12288

/-! Source-cell containment and simple scalar guards at 12288. -/
namespace BstLean.Part264b.N12288
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12288 cell12288)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12288 ⟨10,by decide⟩).lower ∧ (cell12288 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12288 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12288 ⟨11,by decide⟩).lower ∧ (cell12288 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12288 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12288 ⟨12,by decide⟩).lower ∧ (cell12288 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12288 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12288 ⟨13,by decide⟩).lower ∧ (cell12288 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12288 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12288 ⟨14,by decide⟩).lower ∧ (cell12288 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12288 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12288 ⟨15,by decide⟩).lower ∧ (cell12288 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12288 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12288 ⟨16,by decide⟩).lower ∧ (cell12288 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12288 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12288 ⟨17,by decide⟩).lower ∧ (cell12288 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12288 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12288 ⟨18,by decide⟩).lower ∧ (cell12288 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12288 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12288 ⟨19,by decide⟩).lower ∧ (cell12288 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12288 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12288 ⟨20,by decide⟩).lower ∧ (cell12288 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12288 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12288 ⟨21,by decide⟩).lower ∧ (cell12288 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12288 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12288 ⟨22,by decide⟩).lower ∧ (cell12288 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12288 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12288 ⟨23,by decide⟩).lower ∧ (cell12288 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12288 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12288 ⟨24,by decide⟩).lower ∧ (cell12288 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12288 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12288 ⟨25,by decide⟩).lower ∧ (cell12288 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12288 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12288 ⟨26,by decide⟩).lower ∧ (cell12288 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12288 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12288 ⟨27,by decide⟩).lower ∧ (cell12288 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12288 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12288 ⟨28,by decide⟩).lower ∧ (cell12288 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12288 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12288 ⟨29,by decide⟩).lower ∧ (cell12288 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12288 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12288 ⟨30,by decide⟩).lower ∧ (cell12288 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12288 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12288 ⟨31,by decide⟩).lower ∧ (cell12288 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12288 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12288 ⟨32,by decide⟩).lower ∧ (cell12288 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12288 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12288 ⟨33,by decide⟩).lower ∧ (cell12288 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12288 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12288 ⟨34,by decide⟩).lower ∧ (cell12288 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12288 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12288 ⟨35,by decide⟩).lower ∧ (cell12288 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12288 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12288 ⟨36,by decide⟩).lower ∧ (cell12288 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12288 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12288 ⟨37,by decide⟩).lower ∧ (cell12288 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12288 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12288 ⟨38,by decide⟩).lower ∧ (cell12288 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12288 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12288 ⟨39,by decide⟩).lower ∧ (cell12288 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12288 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12288 ⟨40,by decide⟩).lower ∧ (cell12288 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12288 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12288 ⟨41,by decide⟩).lower ∧ (cell12288 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12288 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12288 ⟨42,by decide⟩).lower ∧ (cell12288 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12288 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12288 ⟨43,by decide⟩).lower ∧ (cell12288 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12288 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12288 ⟨44,by decide⟩).lower ∧ (cell12288 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12288 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12288 ⟨45,by decide⟩).lower ∧ (cell12288 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12288 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12288 ⟨46,by decide⟩).lower ∧ (cell12288 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12288 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12288 ⟨47,by decide⟩).lower ∧ (cell12288 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12288 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12288 ⟨48,by decide⟩).lower ∧ (cell12288 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12288 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12288 ⟨49,by decide⟩).lower ∧ (cell12288 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12288 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12288 ⟨50,by decide⟩).lower ∧ (cell12288 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12288 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12288 ⟨51,by decide⟩).lower ∧ (cell12288 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12288 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12288 ⟨52,by decide⟩).lower ∧ (cell12288 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12288 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12288 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12288 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12288,cell12288,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12288 i).lower ∧
    (cell12288 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12288 i).upper ≤ (0.532 : ℝ) ∧
    (cell12288 i).centre ≤ (0.1 : ℝ) ∧ (cell12288 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12288 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12288 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12288

/-! The local source numeric instances at 12288 have no network premises. -/
namespace BstLean.Part264b.N12288
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12288 cell12288)

noncomputable def sourceNumerics12288 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12288 (cell12288 i)
      scalarRow12288.M scalarRow12288.H scalarRow12288.xi := by
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
    energy_allowance := scalarRow12288.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12288]
    centre_nonneg := (scalarRow12288.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12288]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12288
/-! Actual 12289 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12289
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12289 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12289 12289 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12289.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12289 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12289 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12289 := gPlus_lower 12289
end BstLean.Part264b.N12289

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12289
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036408417980 : ℝ) ≤ wn 12289 := by
  have hn : √(12289 : ℝ) ≤ 110.855762141623 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12289 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.855762141623 ≤ 2 / √12289 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260455491 : ℝ) ≤ rhoBar 12289 BstLean.Part154.csC ∧
    rhoBar 12289 BstLean.Part154.csC ≤ 0.000260480166 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036408417980 : ℝ) / (1.295212 * 12289) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12289) := by gcongr
      _ ≤ (0.000260480166 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12289 BstLean.Part154.csC) ≤ 0.001041988514 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12289 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12289 BstLean.Part154.csC) (piBar (rhoBar 12289 BstLean.Part154.csC)) ≤ 0.000198956824 ∧
    cc1 (rhoBar 12289 BstLean.Part154.csC) (piBar (rhoBar 12289 BstLean.Part154.csC)) ≤ 0.000126597483 ∧
    cc2 (rhoBar 12289 BstLean.Part154.csC) ≤ 0.000073490730 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12289 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12289 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12289 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12289 BstLean.Part154.csC * nuR (rhoBar 12289 BstLean.Part154.csC)) ≤ 0.000520977295 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260480166 : ℝ) * 0.001041988514 := by gcongr
      _ ≤ (0.000520977295 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12289 BstLean.Part154.csC) * nuR (rhoBar 12289 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041988514 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12289 BstLean.Part154.csC) * rhoBar 12289 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260480166 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260480166 / 2 + 0.399 * 0.001041988514 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198956824 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520977295 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126597483 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260480166 / 1.414213562 := by gcongr
      _ ≤ (0.000073490730 : ℝ) := by norm_num

end BstLean.Part264b.N12289

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12289
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12289 BstLean.Part154.csC) (piBar (rhoBar 12289 BstLean.Part154.csC)) ≤ 1.70943E-7 := by
  have hr0 : 0 ≤ rhoBar 12289 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12289 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12289 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12289 BstLean.Part154.csC) (piBar (rhoBar 12289 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12289 BstLean.Part154.csC) (piBar (rhoBar 12289 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12289 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198956824 : ℝ) ^ 2 + 0.000126597483 ^ 2 + 3 * 0.000073490730 ^ 2 +
        2 * 0.797885 * 0.000198956824 * 0.000126597483 + 2 * 0.000198956824 * 0.000073490730 +
        4 * 0.797885 * 0.000126597483 * 0.000073490730 := by gcongr
    _ ≤ (1.70943E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12289 BstLean.Part154.csC Θ ≤ 0.002721129412 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12289 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12289 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12289 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12289 BstLean.Part154.csC) (piBar (rhoBar 12289 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12289 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70943E-7 / (0.000260455491 : ℝ) := by gcongr
    _ ≤ 0.002721129412 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12289 BstLean.Part154.csC Θ ≤ 0.003020993183 + 0.000687521472 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12289 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12289 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12289 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260480166 +
        (6863 / 10000) * 0.000260480166 * 12289 * 0.001041988514) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003020993183 + 0.000687521472 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12289 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12289 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12289 0.011 Θ ∧ gammaRatio 12289 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12289 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12289) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12289 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12289 0.011 Θ) :=
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
    badAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12289 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12289 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12289 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12289 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12289 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12289 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12289 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12289 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12289 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12289 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12289 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004120993183 + 0.003408650884 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12289

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12289
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12289 BstLean.Part154.csC) (piBar (rhoBar 12289 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12289 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12289 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12289 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12289 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12289 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12289 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12289 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12289 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12289 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12289 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12289 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12289 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053364346857 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12289) ≤ 0.010772895861 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12289 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010772895861 + 2 * 0.737676 / 12289) := by gcongr
    _ ≤ (0.053364346857 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12289 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12289

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12289
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484360029 : ℝ) ≤ plow 12289 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12289) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417134898)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428592942) : eMP 12289 0.011 xi bn ≤ 0.001229161566 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12289 : ℝ) * (1 - 0.011))) ≤ 0.000607676991 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001428592942 / (12289 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607676991 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607676991 : ℝ) + 3.141593 * 0.053417134898 / (12289 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001229161566 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417134898)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428592942) : PiBarMP 12289 12 0.011 xi bn ≤ 0.163959503275 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12289 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037796731896 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.244369470735 : ℝ) ≤ √((12289 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.855762141622 : ℝ) ≤ √12289 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12289) ≤ 0.125680505854 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037796731896 + 0.053417134898 * 1.772454 / (2 * (110.244369470735 : ℝ))) * (1 + 0.001229161566) +
        8 / (12289 * 110.855762141622) + 0.125680505854 := by gcongr
    _ ≤ (0.163959503275 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417134898)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428592942) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284485819027) :
    parallelOracle 12289 0.011 xi bn cd ≤ 0.164986143686 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12289 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12289 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484360029 : ℝ) ≤ plow 12289 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.855762141622 : ℝ) ≤ √12289 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284485819027 : ℝ) / (2 * 0.560484360029 * 110.855762141622)) * 0.163959503275 +
        0.284485819027 ^ 2 / (2 * 0.560484360029 * 110.855762141622) := by gcongr
    _ ≤ (0.164986143686 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417134898) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428592942)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284485819027) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12289 12289 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484360029 : ℝ) ≤ plow 12289 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.855762141622 : ℝ) ≤ √12289 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12289 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12289 Θ 1.22 ≤ 0.011962395769 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.855762141622 := by gcongr <;> linarith
      _ ≤ (0.011962395769 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12289 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12289 12289 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12289 12289 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12289 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12289 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12289 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12289 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164986143686 + 0.011962395769 + (0.008646 : ℝ) *
        (1 + 2 * (0.284485819027 + 0.011962395769) / (0.560484360029 * 110.855762141622))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12289]

end BstLean.Part264b.N12289

/-! The original eight local profiles supply actual 12289 moment certificates. -/
namespace BstLean.Part264b.N12289
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12289 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053417134898 ∧
    0 ≤ bN 12289 BstLean.Part154.csC (groupTheta g) ∧ bN 12289 BstLean.Part154.csC (groupTheta g) ≤ 0.001428592942 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12289 12289 0.011
      (momentAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12289 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12289 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12289 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231121472170 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12289 0.011
      (momentAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12289 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12289
/-! The actual computed-centre upper energy formula at 12289. -/
namespace BstLean.Part264b.N12289
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12289

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12289
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12289 cell12289)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086794995545
  | 2 => 0.087764295499
  | 3 => 0.088736007903
  | 4 => 0.089712502089
  | 5 => 0.090696606728
  | 6 => 0.091691673042
  | 7 => 0.092701643071
  | 8 => 0.093731122909
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12289 12289 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12289 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12289

/-! Actual upper energy certificates on all 43 source endpoints at 12289. -/
namespace BstLean.Part264b.N12289
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12289 cell12289)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12289 (gMinus 12289) (1 - (cell12289 i).lower) ≤ 1 ∧
    energyUpper 12289 (gMinus 12289) (BstLean.Part211.gPlus 12289)
      (finiteEnergy 12289 12289 0.011) (1 - (cell12289 i).lower) ≤
      (cell12289 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12289) (by norm_num)
        (q := 1 - (cell12289 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12289,cell12289]) (by norm_num [scalarRow12289,cell12289])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12289,cell12289])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12289

/-! Source-cell containment and simple scalar guards at 12289. -/
namespace BstLean.Part264b.N12289
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12289 cell12289)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12289 ⟨10,by decide⟩).lower ∧ (cell12289 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12289 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12289 ⟨11,by decide⟩).lower ∧ (cell12289 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12289 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12289 ⟨12,by decide⟩).lower ∧ (cell12289 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12289 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12289 ⟨13,by decide⟩).lower ∧ (cell12289 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12289 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12289 ⟨14,by decide⟩).lower ∧ (cell12289 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12289 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12289 ⟨15,by decide⟩).lower ∧ (cell12289 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12289 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12289 ⟨16,by decide⟩).lower ∧ (cell12289 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12289 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12289 ⟨17,by decide⟩).lower ∧ (cell12289 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12289 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12289 ⟨18,by decide⟩).lower ∧ (cell12289 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12289 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12289 ⟨19,by decide⟩).lower ∧ (cell12289 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12289 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12289 ⟨20,by decide⟩).lower ∧ (cell12289 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12289 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12289 ⟨21,by decide⟩).lower ∧ (cell12289 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12289 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12289 ⟨22,by decide⟩).lower ∧ (cell12289 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12289 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12289 ⟨23,by decide⟩).lower ∧ (cell12289 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12289 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12289 ⟨24,by decide⟩).lower ∧ (cell12289 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12289 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12289 ⟨25,by decide⟩).lower ∧ (cell12289 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12289 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12289 ⟨26,by decide⟩).lower ∧ (cell12289 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12289 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12289 ⟨27,by decide⟩).lower ∧ (cell12289 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12289 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12289 ⟨28,by decide⟩).lower ∧ (cell12289 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12289 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12289 ⟨29,by decide⟩).lower ∧ (cell12289 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12289 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12289 ⟨30,by decide⟩).lower ∧ (cell12289 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12289 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12289 ⟨31,by decide⟩).lower ∧ (cell12289 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12289 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12289 ⟨32,by decide⟩).lower ∧ (cell12289 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12289 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12289 ⟨33,by decide⟩).lower ∧ (cell12289 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12289 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12289 ⟨34,by decide⟩).lower ∧ (cell12289 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12289 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12289 ⟨35,by decide⟩).lower ∧ (cell12289 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12289 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12289 ⟨36,by decide⟩).lower ∧ (cell12289 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12289 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12289 ⟨37,by decide⟩).lower ∧ (cell12289 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12289 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12289 ⟨38,by decide⟩).lower ∧ (cell12289 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12289 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12289 ⟨39,by decide⟩).lower ∧ (cell12289 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12289 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12289 ⟨40,by decide⟩).lower ∧ (cell12289 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12289 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12289 ⟨41,by decide⟩).lower ∧ (cell12289 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12289 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12289 ⟨42,by decide⟩).lower ∧ (cell12289 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12289 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12289 ⟨43,by decide⟩).lower ∧ (cell12289 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12289 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12289 ⟨44,by decide⟩).lower ∧ (cell12289 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12289 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12289 ⟨45,by decide⟩).lower ∧ (cell12289 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12289 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12289 ⟨46,by decide⟩).lower ∧ (cell12289 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12289 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12289 ⟨47,by decide⟩).lower ∧ (cell12289 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12289 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12289 ⟨48,by decide⟩).lower ∧ (cell12289 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12289 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12289 ⟨49,by decide⟩).lower ∧ (cell12289 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12289 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12289 ⟨50,by decide⟩).lower ∧ (cell12289 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12289 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12289 ⟨51,by decide⟩).lower ∧ (cell12289 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12289 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12289 ⟨52,by decide⟩).lower ∧ (cell12289 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12289 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12289 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12289 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12289,cell12289,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12289 i).lower ∧
    (cell12289 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12289 i).upper ≤ (0.532 : ℝ) ∧
    (cell12289 i).centre ≤ (0.1 : ℝ) ∧ (cell12289 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12289 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12289 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12289

/-! The local source numeric instances at 12289 have no network premises. -/
namespace BstLean.Part264b.N12289
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12289 cell12289)

noncomputable def sourceNumerics12289 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12289 (cell12289 i)
      scalarRow12289.M scalarRow12289.H scalarRow12289.xi := by
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
    energy_allowance := scalarRow12289.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12289]
    centre_nonneg := (scalarRow12289.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12289]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12289
/-! Actual 12290 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12290
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12290 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12290 12290 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12290.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12290 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12290 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12290 := gPlus_lower 12290
end BstLean.Part264b.N12290

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12290
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036406923487 : ℝ) ≤ wn 12290 := by
  have hn : √(12290 : ℝ) ≤ 110.860272415325 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12290 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.860272415325 ≤ 2 / √12290 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260433923 : ℝ) ≤ rhoBar 12290 BstLean.Part154.csC ∧
    rhoBar 12290 BstLean.Part154.csC ≤ 0.000260458972 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036406923487 : ℝ) / (1.295212 * 12290) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12290) := by gcongr
      _ ≤ (0.000260458972 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12290 BstLean.Part154.csC) ≤ 0.001041903727 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12290 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12290 BstLean.Part154.csC) (piBar (rhoBar 12290 BstLean.Part154.csC)) ≤ 0.000198940635 ∧
    cc1 (rhoBar 12290 BstLean.Part154.csC) (piBar (rhoBar 12290 BstLean.Part154.csC)) ≤ 0.000126587182 ∧
    cc2 (rhoBar 12290 BstLean.Part154.csC) ≤ 0.000073484750 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12290 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12290 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12290 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12290 BstLean.Part154.csC * nuR (rhoBar 12290 BstLean.Part154.csC)) ≤ 0.000520934904 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260458972 : ℝ) * 0.001041903727 := by gcongr
      _ ≤ (0.000520934904 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12290 BstLean.Part154.csC) * nuR (rhoBar 12290 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041903727 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12290 BstLean.Part154.csC) * rhoBar 12290 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260458972 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260458972 / 2 + 0.399 * 0.001041903727 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198940635 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520934904 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126587182 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260458972 / 1.414213562 := by gcongr
      _ ≤ (0.000073484750 : ℝ) := by norm_num

end BstLean.Part264b.N12290

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12290
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12290 BstLean.Part154.csC) (piBar (rhoBar 12290 BstLean.Part154.csC)) ≤ 1.70916E-7 := by
  have hr0 : 0 ≤ rhoBar 12290 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12290 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12290 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12290 BstLean.Part154.csC) (piBar (rhoBar 12290 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12290 BstLean.Part154.csC) (piBar (rhoBar 12290 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12290 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198940635 : ℝ) ^ 2 + 0.000126587182 ^ 2 + 3 * 0.000073484750 ^ 2 +
        2 * 0.797885 * 0.000198940635 * 0.000126587182 + 2 * 0.000198940635 * 0.000073484750 +
        4 * 0.797885 * 0.000126587182 * 0.000073484750 := by gcongr
    _ ≤ (1.70916E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12290 BstLean.Part154.csC Θ ≤ 0.002720924933 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12290 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12290 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12290 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12290 BstLean.Part154.csC) (piBar (rhoBar 12290 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12290 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70916E-7 / (0.000260433923 : ℝ) := by gcongr
    _ ≤ 0.002720924933 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12290 BstLean.Part154.csC Θ ≤ 0.003020747369 + 0.000687465532 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12290 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12290 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12290 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260458972 +
        (6863 / 10000) * 0.000260458972 * 12290 * 0.001041903727) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003020747369 + 0.000687465532 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12290 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12290 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12290 0.011 Θ ∧ gammaRatio 12290 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12290 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12290) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12290 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12290 0.011 Θ) :=
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
    badAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12290 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12290 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12290 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12290 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12290 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12290 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12290 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12290 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12290 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12290 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12290 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004120747369 + 0.003408390465 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12290

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12290
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12290 BstLean.Part154.csC) (piBar (rhoBar 12290 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12290 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12290 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12290 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12290 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12290 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12290 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12290 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12290 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12290 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12290 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12290 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12290 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053362151837 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12290) ≤ 0.010772457573 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12290 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010772457573 + 2 * 0.737676 / 12290) := by gcongr
    _ ≤ (0.053362151837 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12290 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12290

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12290
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484408323 : ℝ) ≤ plow 12290 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12290) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053416752364)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428485590) : eMP 12290 0.011 xi bn ≤ 0.001229065236 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12290 : ℝ) * (1 - 0.011))) ≤ 0.000607629437 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001428485590 / (12290 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607629437 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607629437 : ℝ) + 3.141593 * 0.053416752364 / (12290 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001229065236 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053416752364)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428485590) : PiBarMP 12290 12 0.011 xi bn ≤ 0.163952943186 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12290 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037795311747 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.248854869336 : ℝ) ≤ √((12290 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.860272415324 : ℝ) ≤ √12290 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12290) ≤ 0.125675392629 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037795311747 + 0.053416752364 * 1.772454 / (2 * (110.248854869336 : ℝ))) * (1 + 0.001229065236) +
        8 / (12290 * 110.860272415324) + 0.125675392629 := by gcongr
    _ ≤ (0.163952943186 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053416752364)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428485590) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284482796445) :
    parallelOracle 12290 0.011 xi bn cd ≤ 0.164979508896 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12290 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12290 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484408323 : ℝ) ≤ plow 12290 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.860272415324 : ℝ) ≤ √12290 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284482796445 : ℝ) / (2 * 0.560484408323 * 110.860272415324)) * 0.163952943186 +
        0.284482796445 ^ 2 / (2 * 0.560484408323 * 110.860272415324) := by gcongr
    _ ≤ (0.164979508896 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053416752364) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428485590)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284482796445) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12290 12290 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484408323 : ℝ) ≤ plow 12290 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.860272415324 : ℝ) ≤ √12290 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12290 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12290 Θ 1.22 ≤ 0.011961909088 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.860272415324 := by gcongr <;> linarith
      _ ≤ (0.011961909088 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12290 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12290 12290 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12290 12290 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12290 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12290 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12290 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12290 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164979508896 + 0.011961909088 + (0.008646 : ℝ) *
        (1 + 2 * (0.284482796445 + 0.011961909088) / (0.560484408323 * 110.860272415324))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12290]

end BstLean.Part264b.N12290

/-! The original eight local profiles supply actual 12290 moment certificates. -/
namespace BstLean.Part264b.N12290
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12290 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053416752364 ∧
    0 ≤ bN 12290 BstLean.Part154.csC (groupTheta g) ∧ bN 12290 BstLean.Part154.csC (groupTheta g) ≤ 0.001428485590 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12290 12290 0.011
      (momentAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12290 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12290 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12290 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231120644608 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12290 0.011
      (momentAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12290 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12290
/-! The actual computed-centre upper energy formula at 12290. -/
namespace BstLean.Part264b.N12290
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12290

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12290
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12290 cell12290)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086791522943
  | 2 => 0.087760745150
  | 3 => 0.088732366348
  | 4 => 0.089708752958
  | 5 => 0.090692730255
  | 6 => 0.091687645532
  | 7 => 0.092697436308
  | 8 => 0.093726703507
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12290 12290 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12290 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12290

/-! Actual upper energy certificates on all 43 source endpoints at 12290. -/
namespace BstLean.Part264b.N12290
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12290 cell12290)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12290 (gMinus 12290) (1 - (cell12290 i).lower) ≤ 1 ∧
    energyUpper 12290 (gMinus 12290) (BstLean.Part211.gPlus 12290)
      (finiteEnergy 12290 12290 0.011) (1 - (cell12290 i).lower) ≤
      (cell12290 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12290) (by norm_num)
        (q := 1 - (cell12290 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12290,cell12290]) (by norm_num [scalarRow12290,cell12290])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12290,cell12290])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12290

/-! Source-cell containment and simple scalar guards at 12290. -/
namespace BstLean.Part264b.N12290
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12290 cell12290)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12290 ⟨10,by decide⟩).lower ∧ (cell12290 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12290 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12290 ⟨11,by decide⟩).lower ∧ (cell12290 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12290 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12290 ⟨12,by decide⟩).lower ∧ (cell12290 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12290 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12290 ⟨13,by decide⟩).lower ∧ (cell12290 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12290 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12290 ⟨14,by decide⟩).lower ∧ (cell12290 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12290 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12290 ⟨15,by decide⟩).lower ∧ (cell12290 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12290 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12290 ⟨16,by decide⟩).lower ∧ (cell12290 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12290 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12290 ⟨17,by decide⟩).lower ∧ (cell12290 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12290 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12290 ⟨18,by decide⟩).lower ∧ (cell12290 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12290 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12290 ⟨19,by decide⟩).lower ∧ (cell12290 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12290 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12290 ⟨20,by decide⟩).lower ∧ (cell12290 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12290 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12290 ⟨21,by decide⟩).lower ∧ (cell12290 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12290 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12290 ⟨22,by decide⟩).lower ∧ (cell12290 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12290 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12290 ⟨23,by decide⟩).lower ∧ (cell12290 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12290 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12290 ⟨24,by decide⟩).lower ∧ (cell12290 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12290 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12290 ⟨25,by decide⟩).lower ∧ (cell12290 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12290 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12290 ⟨26,by decide⟩).lower ∧ (cell12290 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12290 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12290 ⟨27,by decide⟩).lower ∧ (cell12290 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12290 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12290 ⟨28,by decide⟩).lower ∧ (cell12290 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12290 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12290 ⟨29,by decide⟩).lower ∧ (cell12290 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12290 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12290 ⟨30,by decide⟩).lower ∧ (cell12290 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12290 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12290 ⟨31,by decide⟩).lower ∧ (cell12290 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12290 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12290 ⟨32,by decide⟩).lower ∧ (cell12290 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12290 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12290 ⟨33,by decide⟩).lower ∧ (cell12290 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12290 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12290 ⟨34,by decide⟩).lower ∧ (cell12290 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12290 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12290 ⟨35,by decide⟩).lower ∧ (cell12290 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12290 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12290 ⟨36,by decide⟩).lower ∧ (cell12290 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12290 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12290 ⟨37,by decide⟩).lower ∧ (cell12290 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12290 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12290 ⟨38,by decide⟩).lower ∧ (cell12290 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12290 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12290 ⟨39,by decide⟩).lower ∧ (cell12290 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12290 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12290 ⟨40,by decide⟩).lower ∧ (cell12290 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12290 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12290 ⟨41,by decide⟩).lower ∧ (cell12290 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12290 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12290 ⟨42,by decide⟩).lower ∧ (cell12290 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12290 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12290 ⟨43,by decide⟩).lower ∧ (cell12290 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12290 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12290 ⟨44,by decide⟩).lower ∧ (cell12290 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12290 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12290 ⟨45,by decide⟩).lower ∧ (cell12290 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12290 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12290 ⟨46,by decide⟩).lower ∧ (cell12290 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12290 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12290 ⟨47,by decide⟩).lower ∧ (cell12290 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12290 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12290 ⟨48,by decide⟩).lower ∧ (cell12290 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12290 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12290 ⟨49,by decide⟩).lower ∧ (cell12290 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12290 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12290 ⟨50,by decide⟩).lower ∧ (cell12290 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12290 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12290 ⟨51,by decide⟩).lower ∧ (cell12290 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12290 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12290 ⟨52,by decide⟩).lower ∧ (cell12290 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12290 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12290 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12290 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12290,cell12290,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12290 i).lower ∧
    (cell12290 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12290 i).upper ≤ (0.532 : ℝ) ∧
    (cell12290 i).centre ≤ (0.1 : ℝ) ∧ (cell12290 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12290 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12290 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12290

/-! The local source numeric instances at 12290 have no network premises. -/
namespace BstLean.Part264b.N12290
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12290 cell12290)

noncomputable def sourceNumerics12290 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12290 (cell12290 i)
      scalarRow12290.M scalarRow12290.H scalarRow12290.xi := by
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
    energy_allowance := scalarRow12290.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12290]
    centre_nonneg := (scalarRow12290.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12290]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12290
/-! Actual 12291 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12291
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12291 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12291 12291 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12291.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12291 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12291 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12291 := gPlus_lower 12291
end BstLean.Part264b.N12291

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12291
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036405429177 : ℝ) ≤ wn 12291 := by
  have hn : √(12291 : ℝ) ≤ 110.864782505537 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12291 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.864782505537 ≤ 2 / √12291 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260412359 : ℝ) ≤ rhoBar 12291 BstLean.Part154.csC ∧
    rhoBar 12291 BstLean.Part154.csC ≤ 0.000260437781 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036405429177 : ℝ) / (1.295212 * 12291) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12291) := by gcongr
      _ ≤ (0.000260437781 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12291 BstLean.Part154.csC) ≤ 0.001041818952 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12291 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12291 BstLean.Part154.csC) (piBar (rhoBar 12291 BstLean.Part154.csC)) ≤ 0.000198924448 ∧
    cc1 (rhoBar 12291 BstLean.Part154.csC) (piBar (rhoBar 12291 BstLean.Part154.csC)) ≤ 0.000126576883 ∧
    cc2 (rhoBar 12291 BstLean.Part154.csC) ≤ 0.000073478772 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12291 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12291 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12291 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12291 BstLean.Part154.csC * nuR (rhoBar 12291 BstLean.Part154.csC)) ≤ 0.000520892519 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260437781 : ℝ) * 0.001041818952 := by gcongr
      _ ≤ (0.000520892519 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12291 BstLean.Part154.csC) * nuR (rhoBar 12291 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041818952 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12291 BstLean.Part154.csC) * rhoBar 12291 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260437781 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260437781 / 2 + 0.399 * 0.001041818952 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198924448 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520892519 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126576883 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260437781 / 1.414213562 := by gcongr
      _ ≤ (0.000073478772 : ℝ) := by norm_num

end BstLean.Part264b.N12291

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12291
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12291 BstLean.Part154.csC) (piBar (rhoBar 12291 BstLean.Part154.csC)) ≤ 1.70888E-7 := by
  have hr0 : 0 ≤ rhoBar 12291 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12291 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12291 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12291 BstLean.Part154.csC) (piBar (rhoBar 12291 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12291 BstLean.Part154.csC) (piBar (rhoBar 12291 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12291 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198924448 : ℝ) ^ 2 + 0.000126576883 ^ 2 + 3 * 0.000073478772 ^ 2 +
        2 * 0.797885 * 0.000198924448 * 0.000126576883 + 2 * 0.000198924448 * 0.000073478772 +
        4 * 0.797885 * 0.000126576883 * 0.000073478772 := by gcongr
    _ ≤ (1.70888E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12291 BstLean.Part154.csC Θ ≤ 0.002720704457 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12291 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12291 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12291 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12291 BstLean.Part154.csC) (piBar (rhoBar 12291 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12291 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70888E-7 / (0.000260412359 : ℝ) := by gcongr
    _ ≤ 0.002720704457 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12291 BstLean.Part154.csC Θ ≤ 0.003020501585 + 0.000687409600 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12291 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12291 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12291 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260437781 +
        (6863 / 10000) * 0.000260437781 * 12291 * 0.001041818952) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003020501585 + 0.000687409600 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12291 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12291 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12291 0.011 Θ ∧ gammaRatio 12291 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12291 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12291) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12291 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12291 0.011 Θ) :=
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
    badAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12291 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12291 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12291 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12291 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12291 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12291 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12291 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12291 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12291 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12291 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12291 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004120501585 + 0.003408114057 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12291

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12291
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12291 BstLean.Part154.csC) (piBar (rhoBar 12291 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12291 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12291 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12291 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12291 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12291 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12291 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12291 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12291 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12291 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12291 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12291 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12291 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053359957090 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12291) ≤ 0.010772019339 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12291 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010772019339 + 2 * 0.737676 / 12291) := by gcongr
    _ ≤ (0.053359957090 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12291 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12291

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12291
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484456610 : ℝ) ≤ plow 12291 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12291) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053416361465)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428369840) : eMP 12291 0.011 xi bn ≤ 0.001228965337 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12291 : ℝ) * (1 - 0.011))) ≤ 0.000607580100 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001428369840 / (12291 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607580100 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607580100 : ℝ) + 3.141593 * 0.053416361465 / (12291 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001228965337 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053416361465)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428369840) : PiBarMP 12291 12 0.011 xi bn ≤ 0.163946272227 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12291 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037793780441 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.253340085459 : ℝ) ≤ √((12291 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.864782505536 : ℝ) ≤ √12291 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12291) ≤ 0.125670280029 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037793780441 + 0.053416361465 * 1.772454 / (2 * (110.253340085459 : ℝ))) * (1 + 0.001228965337) +
        8 / (12291 * 110.864782505536) + 0.125670280029 := by gcongr
    _ ≤ (0.163946272227 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053416361465)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428369840) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284479756037) :
    parallelOracle 12291 0.011 xi bn cd ≤ 0.164972762886 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12291 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12291 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484456610 : ℝ) ≤ plow 12291 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.864782505536 : ℝ) ≤ √12291 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284479756037 : ℝ) / (2 * 0.560484456610 * 110.864782505536)) * 0.163946272227 +
        0.284479756037 ^ 2 / (2 * 0.560484456610 * 110.864782505536) := by gcongr
    _ ≤ (0.164972762886 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053416361465) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428369840)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284479756037) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12291 12291 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484456610 : ℝ) ≤ plow 12291 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.864782505536 : ℝ) ≤ √12291 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12291 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12291 Θ 1.22 ≤ 0.011961422465 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.864782505536 := by gcongr <;> linarith
      _ ≤ (0.011961422465 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12291 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12291 12291 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12291 12291 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12291 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12291 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12291 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12291 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164972762886 + 0.011961422465 + (0.008646 : ℝ) *
        (1 + 2 * (0.284479756037 + 0.011961422465) / (0.560484456610 * 110.864782505536))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12291]

end BstLean.Part264b.N12291

/-! The original eight local profiles supply actual 12291 moment certificates. -/
namespace BstLean.Part264b.N12291
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12291 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053416361465 ∧
    0 ≤ bN 12291 BstLean.Part154.csC (groupTheta g) ∧ bN 12291 BstLean.Part154.csC (groupTheta g) ≤ 0.001428369840 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12291 12291 0.011
      (momentAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12291 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12291 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12291 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231119798947 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12291 0.011
      (momentAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12291 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12291
/-! The actual computed-centre upper energy formula at 12291. -/
namespace BstLean.Part264b.N12291
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12291

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12291
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12291 cell12291)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086788052018
  | 2 => 0.087757196554
  | 3 => 0.088728726641
  | 4 => 0.089705005789
  | 5 => 0.090688855885
  | 6 => 0.091683620293
  | 7 => 0.092693232019
  | 8 => 0.093722286822
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12291 12291 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12291 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12291

/-! Actual upper energy certificates on all 43 source endpoints at 12291. -/
namespace BstLean.Part264b.N12291
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12291 cell12291)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12291 (gMinus 12291) (1 - (cell12291 i).lower) ≤ 1 ∧
    energyUpper 12291 (gMinus 12291) (BstLean.Part211.gPlus 12291)
      (finiteEnergy 12291 12291 0.011) (1 - (cell12291 i).lower) ≤
      (cell12291 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12291) (by norm_num)
        (q := 1 - (cell12291 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12291,cell12291]) (by norm_num [scalarRow12291,cell12291])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12291,cell12291])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12291

/-! Source-cell containment and simple scalar guards at 12291. -/
namespace BstLean.Part264b.N12291
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12291 cell12291)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12291 ⟨10,by decide⟩).lower ∧ (cell12291 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12291 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12291 ⟨11,by decide⟩).lower ∧ (cell12291 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12291 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12291 ⟨12,by decide⟩).lower ∧ (cell12291 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12291 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12291 ⟨13,by decide⟩).lower ∧ (cell12291 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12291 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12291 ⟨14,by decide⟩).lower ∧ (cell12291 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12291 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12291 ⟨15,by decide⟩).lower ∧ (cell12291 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12291 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12291 ⟨16,by decide⟩).lower ∧ (cell12291 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12291 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12291 ⟨17,by decide⟩).lower ∧ (cell12291 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12291 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12291 ⟨18,by decide⟩).lower ∧ (cell12291 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12291 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12291 ⟨19,by decide⟩).lower ∧ (cell12291 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12291 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12291 ⟨20,by decide⟩).lower ∧ (cell12291 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12291 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12291 ⟨21,by decide⟩).lower ∧ (cell12291 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12291 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12291 ⟨22,by decide⟩).lower ∧ (cell12291 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12291 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12291 ⟨23,by decide⟩).lower ∧ (cell12291 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12291 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12291 ⟨24,by decide⟩).lower ∧ (cell12291 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12291 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12291 ⟨25,by decide⟩).lower ∧ (cell12291 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12291 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12291 ⟨26,by decide⟩).lower ∧ (cell12291 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12291 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12291 ⟨27,by decide⟩).lower ∧ (cell12291 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12291 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12291 ⟨28,by decide⟩).lower ∧ (cell12291 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12291 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12291 ⟨29,by decide⟩).lower ∧ (cell12291 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12291 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12291 ⟨30,by decide⟩).lower ∧ (cell12291 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12291 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12291 ⟨31,by decide⟩).lower ∧ (cell12291 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12291 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12291 ⟨32,by decide⟩).lower ∧ (cell12291 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12291 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12291 ⟨33,by decide⟩).lower ∧ (cell12291 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12291 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12291 ⟨34,by decide⟩).lower ∧ (cell12291 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12291 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12291 ⟨35,by decide⟩).lower ∧ (cell12291 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12291 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12291 ⟨36,by decide⟩).lower ∧ (cell12291 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12291 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12291 ⟨37,by decide⟩).lower ∧ (cell12291 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12291 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12291 ⟨38,by decide⟩).lower ∧ (cell12291 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12291 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12291 ⟨39,by decide⟩).lower ∧ (cell12291 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12291 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12291 ⟨40,by decide⟩).lower ∧ (cell12291 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12291 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12291 ⟨41,by decide⟩).lower ∧ (cell12291 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12291 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12291 ⟨42,by decide⟩).lower ∧ (cell12291 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12291 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12291 ⟨43,by decide⟩).lower ∧ (cell12291 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12291 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12291 ⟨44,by decide⟩).lower ∧ (cell12291 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12291 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12291 ⟨45,by decide⟩).lower ∧ (cell12291 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12291 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12291 ⟨46,by decide⟩).lower ∧ (cell12291 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12291 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12291 ⟨47,by decide⟩).lower ∧ (cell12291 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12291 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12291 ⟨48,by decide⟩).lower ∧ (cell12291 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12291 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12291 ⟨49,by decide⟩).lower ∧ (cell12291 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12291 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12291 ⟨50,by decide⟩).lower ∧ (cell12291 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12291 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12291 ⟨51,by decide⟩).lower ∧ (cell12291 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12291 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12291 ⟨52,by decide⟩).lower ∧ (cell12291 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12291 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12291 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12291 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12291,cell12291,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12291 i).lower ∧
    (cell12291 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12291 i).upper ≤ (0.532 : ℝ) ∧
    (cell12291 i).centre ≤ (0.1 : ℝ) ∧ (cell12291 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12291 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12291 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12291

/-! The local source numeric instances at 12291 have no network premises. -/
namespace BstLean.Part264b.N12291
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12291 cell12291)

noncomputable def sourceNumerics12291 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12291 (cell12291 i)
      scalarRow12291.M scalarRow12291.H scalarRow12291.xi := by
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
    energy_allowance := scalarRow12291.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12291]
    centre_nonneg := (scalarRow12291.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12291]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12291
/-! Actual 12292 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12292
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12292 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12292 12292 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12292.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12292 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12292 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12292 := gPlus_lower 12292
end BstLean.Part264b.N12292

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12292
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036403935051 : ℝ) ≤ wn 12292 := by
  have hn : √(12292 : ℝ) ≤ 110.869292412282 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12292 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.869292412282 ≤ 2 / √12292 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260390798 : ℝ) ≤ rhoBar 12292 BstLean.Part154.csC ∧
    rhoBar 12292 BstLean.Part154.csC ≤ 0.000260416593 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036403935051 : ℝ) / (1.295212 * 12292) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12292) := by gcongr
      _ ≤ (0.000260416593 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12292 BstLean.Part154.csC) ≤ 0.001041734189 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12292 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12292 BstLean.Part154.csC) (piBar (rhoBar 12292 BstLean.Part154.csC)) ≤ 0.000198908264 ∧
    cc1 (rhoBar 12292 BstLean.Part154.csC) (piBar (rhoBar 12292 BstLean.Part154.csC)) ≤ 0.000126566585 ∧
    cc2 (rhoBar 12292 BstLean.Part154.csC) ≤ 0.000073472794 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12292 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12292 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12292 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12292 BstLean.Part154.csC * nuR (rhoBar 12292 BstLean.Part154.csC)) ≤ 0.000520850140 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260416593 : ℝ) * 0.001041734189 := by gcongr
      _ ≤ (0.000520850140 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12292 BstLean.Part154.csC) * nuR (rhoBar 12292 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041734189 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12292 BstLean.Part154.csC) * rhoBar 12292 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260416593 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260416593 / 2 + 0.399 * 0.001041734189 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198908264 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520850140 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126566585 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260416593 / 1.414213562 := by gcongr
      _ ≤ (0.000073472794 : ℝ) := by norm_num

end BstLean.Part264b.N12292

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12292
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12292 BstLean.Part154.csC) (piBar (rhoBar 12292 BstLean.Part154.csC)) ≤ 1.70860E-7 := by
  have hr0 : 0 ≤ rhoBar 12292 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12292 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12292 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12292 BstLean.Part154.csC) (piBar (rhoBar 12292 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12292 BstLean.Part154.csC) (piBar (rhoBar 12292 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12292 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198908264 : ℝ) ^ 2 + 0.000126566585 ^ 2 + 3 * 0.000073472794 ^ 2 +
        2 * 0.797885 * 0.000198908264 * 0.000126566585 + 2 * 0.000198908264 * 0.000073472794 +
        4 * 0.797885 * 0.000126566585 * 0.000073472794 := by gcongr
    _ ≤ (1.70860E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12292 BstLean.Part154.csC Θ ≤ 0.002720483914 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12292 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12292 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12292 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12292 BstLean.Part154.csC) (piBar (rhoBar 12292 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12292 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70860E-7 / (0.000260390798 : ℝ) := by gcongr
    _ ≤ 0.002720483914 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12292 BstLean.Part154.csC Θ ≤ 0.003020255830 + 0.000687353675 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12292 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12292 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12292 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260416593 +
        (6863 / 10000) * 0.000260416593 * 12292 * 0.001041734189) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003020255830 + 0.000687353675 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12292 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12292 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12292 0.011 Θ ∧ gammaRatio 12292 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12292 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12292) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12292 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12292 0.011 Θ) :=
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
    badAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12292 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12292 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12292 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12292 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12292 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12292 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12292 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12292 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12292 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12292 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12292 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004120255830 + 0.003407837589 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12292

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12292
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12292 BstLean.Part154.csC) (piBar (rhoBar 12292 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12292 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12292 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12292 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12292 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12292 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12292 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12292 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12292 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12292 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12292 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12292 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12292 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053357762610 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12292) ≤ 0.010771581158 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12292 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010771581158 + 2 * 0.737676 / 12292) := by gcongr
    _ ≤ (0.053357762610 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12292 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12292

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12292
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484504889 : ℝ) ≤ plow 12292 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12292) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415970565)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428254055) : eMP 12292 0.011 xi bn ≤ 0.001228865433 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12292 : ℝ) * (1 - 0.011))) ≤ 0.000607530760 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001428254055 / (12292 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607530760 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607530760 : ℝ) + 3.141593 * 0.053415970565 / (12292 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001228865433 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415970565)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428254055) : PiBarMP 12292 12 0.011 xi bn ≤ 0.163939601369 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12292 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037792248610 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.257825119127 : ℝ) ≤ √((12292 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.869292412281 : ℝ) ≤ √12292 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12292) ≤ 0.125665168052 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037792248610 + 0.053415970565 * 1.772454 / (2 * (110.257825119127 : ℝ))) * (1 + 0.001228865433) +
        8 / (12292 * 110.869292412281) + 0.125665168052 := by gcongr
    _ ≤ (0.163939601369 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415970565)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428254055) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284476715890) :
    parallelOracle 12292 0.011 xi bn cd ≤ 0.164966016986 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12292 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12292 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484504889 : ℝ) ≤ plow 12292 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.869292412281 : ℝ) ≤ √12292 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284476715890 : ℝ) / (2 * 0.560484504889 * 110.869292412281)) * 0.163939601369 +
        0.284476715890 ^ 2 / (2 * 0.560484504889 * 110.869292412281) := by gcongr
    _ ≤ (0.164966016986 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415970565) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428254055)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284476715890) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12292 12292 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484504889 : ℝ) ≤ plow 12292 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.869292412281 : ℝ) ≤ √12292 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12292 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12292 Θ 1.22 ≤ 0.011960935902 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.869292412281 := by gcongr <;> linarith
      _ ≤ (0.011960935902 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12292 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12292 12292 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12292 12292 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12292 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12292 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12292 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12292 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164966016986 + 0.011960935902 + (0.008646 : ℝ) *
        (1 + 2 * (0.284476715890 + 0.011960935902) / (0.560484504889 * 110.869292412281))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12292]

end BstLean.Part264b.N12292

/-! The original eight local profiles supply actual 12292 moment certificates. -/
namespace BstLean.Part264b.N12292
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12292 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053415970565 ∧
    0 ≤ bN 12292 BstLean.Part154.csC (groupTheta g) ∧ bN 12292 BstLean.Part154.csC (groupTheta g) ≤ 0.001428254055 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12292 12292 0.011
      (momentAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12292 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12292 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12292 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231118953280 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12292 0.011
      (momentAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12292 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12292
/-! The actual computed-centre upper energy formula at 12292. -/
namespace BstLean.Part264b.N12292
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12292

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12292
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12292 cell12292)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086784582770
  | 2 => 0.087753649711
  | 3 => 0.088725088780
  | 4 => 0.089701260582
  | 5 => 0.090684983614
  | 6 => 0.091679597323
  | 7 => 0.092689030202
  | 8 => 0.093717872851
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12292 12292 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12292 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12292

/-! Actual upper energy certificates on all 43 source endpoints at 12292. -/
namespace BstLean.Part264b.N12292
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12292 cell12292)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12292 (gMinus 12292) (1 - (cell12292 i).lower) ≤ 1 ∧
    energyUpper 12292 (gMinus 12292) (BstLean.Part211.gPlus 12292)
      (finiteEnergy 12292 12292 0.011) (1 - (cell12292 i).lower) ≤
      (cell12292 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12292) (by norm_num)
        (q := 1 - (cell12292 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12292,cell12292]) (by norm_num [scalarRow12292,cell12292])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12292,cell12292])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12292

/-! Source-cell containment and simple scalar guards at 12292. -/
namespace BstLean.Part264b.N12292
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12292 cell12292)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12292 ⟨10,by decide⟩).lower ∧ (cell12292 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12292 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12292 ⟨11,by decide⟩).lower ∧ (cell12292 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12292 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12292 ⟨12,by decide⟩).lower ∧ (cell12292 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12292 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12292 ⟨13,by decide⟩).lower ∧ (cell12292 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12292 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12292 ⟨14,by decide⟩).lower ∧ (cell12292 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12292 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12292 ⟨15,by decide⟩).lower ∧ (cell12292 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12292 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12292 ⟨16,by decide⟩).lower ∧ (cell12292 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12292 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12292 ⟨17,by decide⟩).lower ∧ (cell12292 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12292 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12292 ⟨18,by decide⟩).lower ∧ (cell12292 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12292 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12292 ⟨19,by decide⟩).lower ∧ (cell12292 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12292 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12292 ⟨20,by decide⟩).lower ∧ (cell12292 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12292 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12292 ⟨21,by decide⟩).lower ∧ (cell12292 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12292 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12292 ⟨22,by decide⟩).lower ∧ (cell12292 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12292 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12292 ⟨23,by decide⟩).lower ∧ (cell12292 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12292 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12292 ⟨24,by decide⟩).lower ∧ (cell12292 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12292 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12292 ⟨25,by decide⟩).lower ∧ (cell12292 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12292 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12292 ⟨26,by decide⟩).lower ∧ (cell12292 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12292 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12292 ⟨27,by decide⟩).lower ∧ (cell12292 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12292 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12292 ⟨28,by decide⟩).lower ∧ (cell12292 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12292 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12292 ⟨29,by decide⟩).lower ∧ (cell12292 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12292 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12292 ⟨30,by decide⟩).lower ∧ (cell12292 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12292 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12292 ⟨31,by decide⟩).lower ∧ (cell12292 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12292 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12292 ⟨32,by decide⟩).lower ∧ (cell12292 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12292 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12292 ⟨33,by decide⟩).lower ∧ (cell12292 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12292 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12292 ⟨34,by decide⟩).lower ∧ (cell12292 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12292 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12292 ⟨35,by decide⟩).lower ∧ (cell12292 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12292 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12292 ⟨36,by decide⟩).lower ∧ (cell12292 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12292 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12292 ⟨37,by decide⟩).lower ∧ (cell12292 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12292 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12292 ⟨38,by decide⟩).lower ∧ (cell12292 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12292 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12292 ⟨39,by decide⟩).lower ∧ (cell12292 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12292 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12292 ⟨40,by decide⟩).lower ∧ (cell12292 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12292 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12292 ⟨41,by decide⟩).lower ∧ (cell12292 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12292 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12292 ⟨42,by decide⟩).lower ∧ (cell12292 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12292 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12292 ⟨43,by decide⟩).lower ∧ (cell12292 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12292 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12292 ⟨44,by decide⟩).lower ∧ (cell12292 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12292 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12292 ⟨45,by decide⟩).lower ∧ (cell12292 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12292 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12292 ⟨46,by decide⟩).lower ∧ (cell12292 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12292 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12292 ⟨47,by decide⟩).lower ∧ (cell12292 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12292 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12292 ⟨48,by decide⟩).lower ∧ (cell12292 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12292 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12292 ⟨49,by decide⟩).lower ∧ (cell12292 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12292 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12292 ⟨50,by decide⟩).lower ∧ (cell12292 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12292 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12292 ⟨51,by decide⟩).lower ∧ (cell12292 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12292 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12292 ⟨52,by decide⟩).lower ∧ (cell12292 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12292 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12292 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12292 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12292,cell12292,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12292 i).lower ∧
    (cell12292 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12292 i).upper ≤ (0.532 : ℝ) ∧
    (cell12292 i).centre ≤ (0.1 : ℝ) ∧ (cell12292 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12292 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12292 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12292

/-! The local source numeric instances at 12292 have no network premises. -/
namespace BstLean.Part264b.N12292
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12292 cell12292)

noncomputable def sourceNumerics12292 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12292 (cell12292 i)
      scalarRow12292.M scalarRow12292.H scalarRow12292.xi := by
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
    energy_allowance := scalarRow12292.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12292]
    centre_nonneg := (scalarRow12292.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12292]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12292
/-! Actual 12293 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12293
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12293 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12293 12293 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12293.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12293 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12293 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12293 := gPlus_lower 12293
end BstLean.Part264b.N12293

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12293
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036402441108 : ℝ) ≤ wn 12293 := by
  have hn : √(12293 : ℝ) ≤ 110.873802135582 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12293 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.873802135582 ≤ 2 / √12293 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260369241 : ℝ) ≤ rhoBar 12293 BstLean.Part154.csC ∧
    rhoBar 12293 BstLean.Part154.csC ≤ 0.000260395409 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036402441108 : ℝ) / (1.295212 * 12293) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12293) := by gcongr
      _ ≤ (0.000260395409 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12293 BstLean.Part154.csC) ≤ 0.001041649442 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12293 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12293 BstLean.Part154.csC) (piBar (rhoBar 12293 BstLean.Part154.csC)) ≤ 0.000198892083 ∧
    cc1 (rhoBar 12293 BstLean.Part154.csC) (piBar (rhoBar 12293 BstLean.Part154.csC)) ≤ 0.000126556289 ∧
    cc2 (rhoBar 12293 BstLean.Part154.csC) ≤ 0.000073466817 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12293 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12293 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12293 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12293 BstLean.Part154.csC * nuR (rhoBar 12293 BstLean.Part154.csC)) ≤ 0.000520807770 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260395409 : ℝ) * 0.001041649442 := by gcongr
      _ ≤ (0.000520807770 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12293 BstLean.Part154.csC) * nuR (rhoBar 12293 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041649442 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12293 BstLean.Part154.csC) * rhoBar 12293 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260395409 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260395409 / 2 + 0.399 * 0.001041649442 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198892083 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520807770 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126556289 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260395409 / 1.414213562 := by gcongr
      _ ≤ (0.000073466817 : ℝ) := by norm_num

end BstLean.Part264b.N12293

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12293
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12293 BstLean.Part154.csC) (piBar (rhoBar 12293 BstLean.Part154.csC)) ≤ 1.70832E-7 := by
  have hr0 : 0 ≤ rhoBar 12293 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12293 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12293 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12293 BstLean.Part154.csC) (piBar (rhoBar 12293 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12293 BstLean.Part154.csC) (piBar (rhoBar 12293 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12293 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198892083 : ℝ) ^ 2 + 0.000126556289 ^ 2 + 3 * 0.000073466817 ^ 2 +
        2 * 0.797885 * 0.000198892083 * 0.000126556289 + 2 * 0.000198892083 * 0.000073466817 +
        4 * 0.797885 * 0.000126556289 * 0.000073466817 := by gcongr
    _ ≤ (1.70832E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12293 BstLean.Part154.csC Θ ≤ 0.002720263292 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12293 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12293 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12293 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12293 BstLean.Part154.csC) (piBar (rhoBar 12293 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12293 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70832E-7 / (0.000260369241 : ℝ) := by gcongr
    _ ≤ 0.002720263292 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12293 BstLean.Part154.csC Θ ≤ 0.003020010129 + 0.000687297761 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12293 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12293 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12293 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260395409 +
        (6863 / 10000) * 0.000260395409 * 12293 * 0.001041649442) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003020010129 + 0.000687297761 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12293 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12293 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12293 0.011 Θ ∧ gammaRatio 12293 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12293 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12293) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12293 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12293 0.011 Θ) :=
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
    badAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12293 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12293 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12293 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12293 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12293 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12293 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12293 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12293 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12293 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12293 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12293 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004120010129 + 0.003407561053 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12293

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12293
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12293 BstLean.Part154.csC) (piBar (rhoBar 12293 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12293 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12293 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12293 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12293 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12293 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12293 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12293 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12293 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12293 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12293 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12293 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12293 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053355568397 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12293) ≤ 0.010771143030 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12293 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010771143030 + 2 * 0.737676 / 12293) := by gcongr
    _ ≤ (0.053355568397 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12293 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12293

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12293
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484553160 : ℝ) ≤ plow 12293 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12293) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415579682)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428138229) : eMP 12293 0.011 xi bn ≤ 0.001228765521 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12293 : ℝ) * (1 - 0.011))) ≤ 0.000607481416 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001428138229 / (12293 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607481416 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607481416 : ℝ) + 3.141593 * 0.053415579682 / (12293 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001228765521 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415579682)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428138229) : PiBarMP 12293 12 0.011 xi bn ≤ 0.163932930532 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12293 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037790716175 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.262309970361 : ℝ) ≤ √((12293 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.873802135581 : ℝ) ≤ √12293 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12293) ≤ 0.125660056699 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037790716175 + 0.053415579682 * 1.772454 / (2 * (110.262309970361 : ℝ))) * (1 + 0.001228765521) +
        8 / (12293 * 110.873802135581) + 0.125660056699 := by gcongr
    _ ≤ (0.163932930532 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415579682)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428138229) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284473676044) :
    parallelOracle 12293 0.011 xi bn cd ≤ 0.164959271118 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12293 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12293 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484553160 : ℝ) ≤ plow 12293 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.873802135581 : ℝ) ≤ √12293 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284473676044 : ℝ) / (2 * 0.560484553160 * 110.873802135581)) * 0.163932930532 +
        0.284473676044 ^ 2 / (2 * 0.560484553160 * 110.873802135581) := by gcongr
    _ ≤ (0.164959271118 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415579682) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428138229)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284473676044) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12293 12293 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484553160 : ℝ) ≤ plow 12293 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.873802135581 : ℝ) ≤ √12293 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12293 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12293 Θ 1.22 ≤ 0.011960449398 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.873802135581 := by gcongr <;> linarith
      _ ≤ (0.011960449398 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12293 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12293 12293 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12293 12293 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12293 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12293 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12293 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12293 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164959271118 + 0.011960449398 + (0.008646 : ℝ) *
        (1 + 2 * (0.284473676044 + 0.011960449398) / (0.560484553160 * 110.873802135581))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12293]

end BstLean.Part264b.N12293

/-! The original eight local profiles supply actual 12293 moment certificates. -/
namespace BstLean.Part264b.N12293
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12293 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053415579682 ∧
    0 ≤ bN 12293 BstLean.Part154.csC (groupTheta g) ∧ bN 12293 BstLean.Part154.csC (groupTheta g) ≤ 0.001428138229 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12293 12293 0.011
      (momentAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12293 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12293 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12293 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231118107647 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12293 0.011
      (momentAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12293 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12293
/-! The actual computed-centre upper energy formula at 12293. -/
namespace BstLean.Part264b.N12293
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12293

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12293
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12293 cell12293)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086781115197
  | 2 => 0.087750104619
  | 3 => 0.088721452763
  | 4 => 0.089697517332
  | 5 => 0.090681113442
  | 6 => 0.091675576619
  | 7 => 0.092684830853
  | 8 => 0.093713461591
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12293 12293 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12293 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12293

/-! Actual upper energy certificates on all 43 source endpoints at 12293. -/
namespace BstLean.Part264b.N12293
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12293 cell12293)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12293 (gMinus 12293) (1 - (cell12293 i).lower) ≤ 1 ∧
    energyUpper 12293 (gMinus 12293) (BstLean.Part211.gPlus 12293)
      (finiteEnergy 12293 12293 0.011) (1 - (cell12293 i).lower) ≤
      (cell12293 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12293) (by norm_num)
        (q := 1 - (cell12293 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12293,cell12293]) (by norm_num [scalarRow12293,cell12293])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12293,cell12293])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12293

/-! Source-cell containment and simple scalar guards at 12293. -/
namespace BstLean.Part264b.N12293
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12293 cell12293)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12293 ⟨10,by decide⟩).lower ∧ (cell12293 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12293 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12293 ⟨11,by decide⟩).lower ∧ (cell12293 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12293 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12293 ⟨12,by decide⟩).lower ∧ (cell12293 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12293 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12293 ⟨13,by decide⟩).lower ∧ (cell12293 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12293 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12293 ⟨14,by decide⟩).lower ∧ (cell12293 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12293 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12293 ⟨15,by decide⟩).lower ∧ (cell12293 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12293 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12293 ⟨16,by decide⟩).lower ∧ (cell12293 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12293 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12293 ⟨17,by decide⟩).lower ∧ (cell12293 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12293 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12293 ⟨18,by decide⟩).lower ∧ (cell12293 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12293 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12293 ⟨19,by decide⟩).lower ∧ (cell12293 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12293 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12293 ⟨20,by decide⟩).lower ∧ (cell12293 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12293 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12293 ⟨21,by decide⟩).lower ∧ (cell12293 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12293 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12293 ⟨22,by decide⟩).lower ∧ (cell12293 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12293 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12293 ⟨23,by decide⟩).lower ∧ (cell12293 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12293 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12293 ⟨24,by decide⟩).lower ∧ (cell12293 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12293 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12293 ⟨25,by decide⟩).lower ∧ (cell12293 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12293 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12293 ⟨26,by decide⟩).lower ∧ (cell12293 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12293 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12293 ⟨27,by decide⟩).lower ∧ (cell12293 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12293 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12293 ⟨28,by decide⟩).lower ∧ (cell12293 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12293 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12293 ⟨29,by decide⟩).lower ∧ (cell12293 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12293 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12293 ⟨30,by decide⟩).lower ∧ (cell12293 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12293 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12293 ⟨31,by decide⟩).lower ∧ (cell12293 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12293 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12293 ⟨32,by decide⟩).lower ∧ (cell12293 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12293 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12293 ⟨33,by decide⟩).lower ∧ (cell12293 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12293 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12293 ⟨34,by decide⟩).lower ∧ (cell12293 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12293 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12293 ⟨35,by decide⟩).lower ∧ (cell12293 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12293 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12293 ⟨36,by decide⟩).lower ∧ (cell12293 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12293 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12293 ⟨37,by decide⟩).lower ∧ (cell12293 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12293 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12293 ⟨38,by decide⟩).lower ∧ (cell12293 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12293 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12293 ⟨39,by decide⟩).lower ∧ (cell12293 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12293 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12293 ⟨40,by decide⟩).lower ∧ (cell12293 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12293 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12293 ⟨41,by decide⟩).lower ∧ (cell12293 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12293 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12293 ⟨42,by decide⟩).lower ∧ (cell12293 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12293 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12293 ⟨43,by decide⟩).lower ∧ (cell12293 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12293 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12293 ⟨44,by decide⟩).lower ∧ (cell12293 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12293 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12293 ⟨45,by decide⟩).lower ∧ (cell12293 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12293 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12293 ⟨46,by decide⟩).lower ∧ (cell12293 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12293 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12293 ⟨47,by decide⟩).lower ∧ (cell12293 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12293 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12293 ⟨48,by decide⟩).lower ∧ (cell12293 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12293 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12293 ⟨49,by decide⟩).lower ∧ (cell12293 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12293 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12293 ⟨50,by decide⟩).lower ∧ (cell12293 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12293 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12293 ⟨51,by decide⟩).lower ∧ (cell12293 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12293 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12293 ⟨52,by decide⟩).lower ∧ (cell12293 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12293 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12293 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12293 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12293,cell12293,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12293 i).lower ∧
    (cell12293 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12293 i).upper ≤ (0.532 : ℝ) ∧
    (cell12293 i).centre ≤ (0.1 : ℝ) ∧ (cell12293 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12293 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12293 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12293

/-! The local source numeric instances at 12293 have no network premises. -/
namespace BstLean.Part264b.N12293
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12293 cell12293)

noncomputable def sourceNumerics12293 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12293 (cell12293 i)
      scalarRow12293.M scalarRow12293.H scalarRow12293.xi := by
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
    energy_allowance := scalarRow12293.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12293]
    centre_nonneg := (scalarRow12293.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12293]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12293
/-! Actual 12294 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12294
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12294 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12294 12294 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12294.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12294 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12294 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12294 := gPlus_lower 12294
end BstLean.Part264b.N12294

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12294
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036400947348 : ℝ) ≤ wn 12294 := by
  have hn : √(12294 : ℝ) ≤ 110.878311675458 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12294 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.878311675458 ≤ 2 / √12294 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260347687 : ℝ) ≤ rhoBar 12294 BstLean.Part154.csC ∧
    rhoBar 12294 BstLean.Part154.csC ≤ 0.000260374228 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036400947348 : ℝ) / (1.295212 * 12294) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12294) := by gcongr
      _ ≤ (0.000260374228 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12294 BstLean.Part154.csC) ≤ 0.001041564707 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12294 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12294 BstLean.Part154.csC) (piBar (rhoBar 12294 BstLean.Part154.csC)) ≤ 0.000198875904 ∧
    cc1 (rhoBar 12294 BstLean.Part154.csC) (piBar (rhoBar 12294 BstLean.Part154.csC)) ≤ 0.000126545994 ∧
    cc2 (rhoBar 12294 BstLean.Part154.csC) ≤ 0.000073460841 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12294 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12294 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12294 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12294 BstLean.Part154.csC * nuR (rhoBar 12294 BstLean.Part154.csC)) ≤ 0.000520765405 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260374228 : ℝ) * 0.001041564707 := by gcongr
      _ ≤ (0.000520765405 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12294 BstLean.Part154.csC) * nuR (rhoBar 12294 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041564707 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12294 BstLean.Part154.csC) * rhoBar 12294 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260374228 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260374228 / 2 + 0.399 * 0.001041564707 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198875904 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520765405 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126545994 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260374228 / 1.414213562 := by gcongr
      _ ≤ (0.000073460841 : ℝ) := by norm_num

end BstLean.Part264b.N12294

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12294
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12294 BstLean.Part154.csC) (piBar (rhoBar 12294 BstLean.Part154.csC)) ≤ 1.70804E-7 := by
  have hr0 : 0 ≤ rhoBar 12294 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12294 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12294 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12294 BstLean.Part154.csC) (piBar (rhoBar 12294 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12294 BstLean.Part154.csC) (piBar (rhoBar 12294 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12294 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198875904 : ℝ) ^ 2 + 0.000126545994 ^ 2 + 3 * 0.000073460841 ^ 2 +
        2 * 0.797885 * 0.000198875904 * 0.000126545994 + 2 * 0.000198875904 * 0.000073460841 +
        4 * 0.797885 * 0.000126545994 * 0.000073460841 := by gcongr
    _ ≤ (1.70804E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12294 BstLean.Part154.csC Θ ≤ 0.002720042603 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12294 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12294 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12294 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12294 BstLean.Part154.csC) (piBar (rhoBar 12294 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12294 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70804E-7 / (0.000260347687 : ℝ) := by gcongr
    _ ≤ 0.002720042603 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12294 BstLean.Part154.csC Θ ≤ 0.003019764456 + 0.000687241855 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12294 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12294 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12294 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260374228 +
        (6863 / 10000) * 0.000260374228 * 12294 * 0.001041564707) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003019764456 + 0.000687241855 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12294 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12294 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12294 0.011 Θ ∧ gammaRatio 12294 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12294 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12294) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12294 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12294 0.011 Θ) :=
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
    badAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12294 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12294 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12294 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12294 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12294 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12294 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12294 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12294 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12294 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12294 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12294 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004119764456 + 0.003407284458 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12294

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12294
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12294 BstLean.Part154.csC) (piBar (rhoBar 12294 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12294 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12294 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12294 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12294 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12294 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12294 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12294 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12294 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12294 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12294 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12294 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12294 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053353374457 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12294) ≤ 0.010770704956 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12294 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010770704956 + 2 * 0.737676 / 12294) := by gcongr
    _ ≤ (0.053353374457 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12294 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12294

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12294
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484601423 : ℝ) ≤ plow 12294 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12294) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415188797)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428022367) : eMP 12294 0.011 xi bn ≤ 0.001228665599 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12294 : ℝ) * (1 - 0.011))) ≤ 0.000607432067 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001428022367 / (12294 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607432067 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607432067 : ℝ) + 3.141593 * 0.053415188797 / (12294 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001228665599 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415188797)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428022367) : PiBarMP 12294 12 0.011 xi bn ≤ 0.163926259784 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12294 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037789183202 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.266794639184 : ℝ) ≤ √((12294 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.878311675457 : ℝ) ≤ √12294 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12294) ≤ 0.125654945970 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037789183202 + 0.053415188797 * 1.772454 / (2 * (110.266794639184 : ℝ))) * (1 + 0.001228665599) +
        8 / (12294 * 110.878311675457) + 0.125654945970 := by gcongr
    _ ≤ (0.163926259784 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415188797)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428022367) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284470636463) :
    parallelOracle 12294 0.011 xi bn cd ≤ 0.164952525349 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12294 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12294 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484601423 : ℝ) ≤ plow 12294 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.878311675457 : ℝ) ≤ √12294 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284470636463 : ℝ) / (2 * 0.560484601423 * 110.878311675457)) * 0.163926259784 +
        0.284470636463 ^ 2 / (2 * 0.560484601423 * 110.878311675457) := by gcongr
    _ ≤ (0.164952525349 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053415188797) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428022367)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284470636463) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12294 12294 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484601423 : ℝ) ≤ plow 12294 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.878311675457 : ℝ) ≤ √12294 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12294 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12294 Θ 1.22 ≤ 0.011959962954 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.878311675457 := by gcongr <;> linarith
      _ ≤ (0.011959962954 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12294 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12294 12294 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12294 12294 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12294 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12294 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12294 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12294 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164952525349 + 0.011959962954 + (0.008646 : ℝ) *
        (1 + 2 * (0.284470636463 + 0.011959962954) / (0.560484601423 * 110.878311675457))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12294]

end BstLean.Part264b.N12294

/-! The original eight local profiles supply actual 12294 moment certificates. -/
namespace BstLean.Part264b.N12294
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12294 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053415188797 ∧
    0 ≤ bN 12294 BstLean.Part154.csC (groupTheta g) ∧ bN 12294 BstLean.Part154.csC (groupTheta g) ≤ 0.001428022367 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12294 12294 0.011
      (momentAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12294 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12294 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12294 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231117262006 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12294 0.011
      (momentAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12294 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12294
/-! The actual computed-centre upper energy formula at 12294. -/
namespace BstLean.Part264b.N12294
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12294

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12294
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12294 cell12294)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086777649296
  | 2 => 0.087746561275
  | 3 => 0.088717818588
  | 4 => 0.089693776039
  | 5 => 0.090677245365
  | 6 => 0.091671558179
  | 7 => 0.092680633971
  | 8 => 0.093709053039
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12294 12294 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12294 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12294

/-! Actual upper energy certificates on all 43 source endpoints at 12294. -/
namespace BstLean.Part264b.N12294
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12294 cell12294)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12294 (gMinus 12294) (1 - (cell12294 i).lower) ≤ 1 ∧
    energyUpper 12294 (gMinus 12294) (BstLean.Part211.gPlus 12294)
      (finiteEnergy 12294 12294 0.011) (1 - (cell12294 i).lower) ≤
      (cell12294 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12294) (by norm_num)
        (q := 1 - (cell12294 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12294,cell12294]) (by norm_num [scalarRow12294,cell12294])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12294,cell12294])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12294

/-! Source-cell containment and simple scalar guards at 12294. -/
namespace BstLean.Part264b.N12294
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12294 cell12294)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12294 ⟨10,by decide⟩).lower ∧ (cell12294 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12294 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12294 ⟨11,by decide⟩).lower ∧ (cell12294 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12294 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12294 ⟨12,by decide⟩).lower ∧ (cell12294 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12294 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12294 ⟨13,by decide⟩).lower ∧ (cell12294 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12294 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12294 ⟨14,by decide⟩).lower ∧ (cell12294 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12294 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12294 ⟨15,by decide⟩).lower ∧ (cell12294 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12294 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12294 ⟨16,by decide⟩).lower ∧ (cell12294 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12294 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12294 ⟨17,by decide⟩).lower ∧ (cell12294 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12294 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12294 ⟨18,by decide⟩).lower ∧ (cell12294 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12294 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12294 ⟨19,by decide⟩).lower ∧ (cell12294 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12294 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12294 ⟨20,by decide⟩).lower ∧ (cell12294 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12294 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12294 ⟨21,by decide⟩).lower ∧ (cell12294 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12294 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12294 ⟨22,by decide⟩).lower ∧ (cell12294 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12294 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12294 ⟨23,by decide⟩).lower ∧ (cell12294 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12294 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12294 ⟨24,by decide⟩).lower ∧ (cell12294 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12294 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12294 ⟨25,by decide⟩).lower ∧ (cell12294 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12294 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12294 ⟨26,by decide⟩).lower ∧ (cell12294 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12294 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12294 ⟨27,by decide⟩).lower ∧ (cell12294 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12294 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12294 ⟨28,by decide⟩).lower ∧ (cell12294 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12294 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12294 ⟨29,by decide⟩).lower ∧ (cell12294 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12294 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12294 ⟨30,by decide⟩).lower ∧ (cell12294 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12294 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12294 ⟨31,by decide⟩).lower ∧ (cell12294 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12294 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12294 ⟨32,by decide⟩).lower ∧ (cell12294 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12294 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12294 ⟨33,by decide⟩).lower ∧ (cell12294 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12294 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12294 ⟨34,by decide⟩).lower ∧ (cell12294 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12294 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12294 ⟨35,by decide⟩).lower ∧ (cell12294 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12294 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12294 ⟨36,by decide⟩).lower ∧ (cell12294 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12294 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12294 ⟨37,by decide⟩).lower ∧ (cell12294 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12294 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12294 ⟨38,by decide⟩).lower ∧ (cell12294 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12294 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12294 ⟨39,by decide⟩).lower ∧ (cell12294 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12294 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12294 ⟨40,by decide⟩).lower ∧ (cell12294 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12294 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12294 ⟨41,by decide⟩).lower ∧ (cell12294 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12294 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12294 ⟨42,by decide⟩).lower ∧ (cell12294 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12294 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12294 ⟨43,by decide⟩).lower ∧ (cell12294 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12294 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12294 ⟨44,by decide⟩).lower ∧ (cell12294 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12294 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12294 ⟨45,by decide⟩).lower ∧ (cell12294 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12294 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12294 ⟨46,by decide⟩).lower ∧ (cell12294 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12294 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12294 ⟨47,by decide⟩).lower ∧ (cell12294 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12294 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12294 ⟨48,by decide⟩).lower ∧ (cell12294 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12294 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12294 ⟨49,by decide⟩).lower ∧ (cell12294 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12294 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12294 ⟨50,by decide⟩).lower ∧ (cell12294 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12294 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12294 ⟨51,by decide⟩).lower ∧ (cell12294 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12294 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12294 ⟨52,by decide⟩).lower ∧ (cell12294 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12294 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12294 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12294 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12294,cell12294,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12294 i).lower ∧
    (cell12294 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12294 i).upper ≤ (0.532 : ℝ) ∧
    (cell12294 i).centre ≤ (0.1 : ℝ) ∧ (cell12294 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12294 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12294 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12294

/-! The local source numeric instances at 12294 have no network premises. -/
namespace BstLean.Part264b.N12294
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12294 cell12294)

noncomputable def sourceNumerics12294 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12294 (cell12294 i)
      scalarRow12294.M scalarRow12294.H scalarRow12294.xi := by
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
    energy_allowance := scalarRow12294.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12294]
    centre_nonneg := (scalarRow12294.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12294]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12294
/-! Actual 12295 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12295
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12295 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12295 12295 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12295.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12295 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12295 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12295 := gPlus_lower 12295
end BstLean.Part264b.N12295

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12295
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036399453772 : ℝ) ≤ wn 12295 := by
  have hn : √(12295 : ℝ) ≤ 110.882821031935 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12295 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.882821031935 ≤ 2 / √12295 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260326137 : ℝ) ≤ rhoBar 12295 BstLean.Part154.csC ∧
    rhoBar 12295 BstLean.Part154.csC ≤ 0.000260353051 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036399453772 : ℝ) / (1.295212 * 12295) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12295) := by gcongr
      _ ≤ (0.000260353051 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12295 BstLean.Part154.csC) ≤ 0.001041479988 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12295 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12295 BstLean.Part154.csC) (piBar (rhoBar 12295 BstLean.Part154.csC)) ≤ 0.000198859728 ∧
    cc1 (rhoBar 12295 BstLean.Part154.csC) (piBar (rhoBar 12295 BstLean.Part154.csC)) ≤ 0.000126535701 ∧
    cc2 (rhoBar 12295 BstLean.Part154.csC) ≤ 0.000073454866 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12295 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12295 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12295 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12295 BstLean.Part154.csC * nuR (rhoBar 12295 BstLean.Part154.csC)) ≤ 0.000520723048 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260353051 : ℝ) * 0.001041479988 := by gcongr
      _ ≤ (0.000520723048 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12295 BstLean.Part154.csC) * nuR (rhoBar 12295 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041479988 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12295 BstLean.Part154.csC) * rhoBar 12295 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260353051 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260353051 / 2 + 0.399 * 0.001041479988 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198859728 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520723048 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126535701 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260353051 / 1.414213562 := by gcongr
      _ ≤ (0.000073454866 : ℝ) := by norm_num

end BstLean.Part264b.N12295

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12295
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12295 BstLean.Part154.csC) (piBar (rhoBar 12295 BstLean.Part154.csC)) ≤ 1.70777E-7 := by
  have hr0 : 0 ≤ rhoBar 12295 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12295 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12295 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12295 BstLean.Part154.csC) (piBar (rhoBar 12295 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12295 BstLean.Part154.csC) (piBar (rhoBar 12295 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12295 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198859728 : ℝ) ^ 2 + 0.000126535701 ^ 2 + 3 * 0.000073454866 ^ 2 +
        2 * 0.797885 * 0.000198859728 * 0.000126535701 + 2 * 0.000198859728 * 0.000073454866 +
        4 * 0.797885 * 0.000126535701 * 0.000073454866 := by gcongr
    _ ≤ (1.70777E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12295 BstLean.Part154.csC Θ ≤ 0.002719837761 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12295 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12295 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12295 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12295 BstLean.Part154.csC) (piBar (rhoBar 12295 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12295 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70777E-7 / (0.000260326137 : ℝ) := by gcongr
    _ ≤ 0.002719837761 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12295 BstLean.Part154.csC Θ ≤ 0.003019518837 + 0.000687185960 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12295 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12295 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12295 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260353051 +
        (6863 / 10000) * 0.000260353051 * 12295 * 0.001041479988) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003019518837 + 0.000687185960 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12295 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12295 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12295 0.011 Θ ∧ gammaRatio 12295 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12295 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12295) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12295 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12295 0.011 Θ) :=
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
    badAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12295 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12295 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12295 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12295 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12295 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12295 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12295 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12295 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12295 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12295 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12295 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004119518837 + 0.003407023721 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12295

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12295
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12295 BstLean.Part154.csC) (piBar (rhoBar 12295 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12295 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12295 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12295 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12295 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12295 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12295 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12295 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12295 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12295 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12295 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12295 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12295 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053351180789 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12295) ≤ 0.010770266936 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12295 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010770266936 + 2 * 0.737676 / 12295) := by gcongr
    _ ≤ (0.053351180789 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12295 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12295

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12295
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484649678 : ℝ) ≤ plow 12295 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12295) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414806291)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427914825) : eMP 12295 0.011 xi bn ≤ 0.001228569230 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12295 : ℝ) * (1 - 0.011))) ≤ 0.000607384493 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001427914825 / (12295 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607384493 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607384493 : ℝ) + 3.141593 * 0.053414806291 / (12295 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001228569230 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414806291)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427914825) : PiBarMP 12295 12 0.011 xi bn ≤ 0.163919700024 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12295 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037787760254 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.271279125618 : ℝ) ≤ √((12295 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.882821031934 : ℝ) ≤ √12295 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12295) ≤ 0.125649835864 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037787760254 + 0.053414806291 * 1.772454 / (2 * (110.271279125618 : ℝ))) * (1 + 0.001228569230) +
        8 / (12295 * 110.882821031934) + 0.125649835864 := by gcongr
    _ ≤ (0.163919700024 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414806291)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427914825) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284467615279) :
    parallelOracle 12295 0.011 xi bn cd ≤ 0.164945890939 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12295 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12295 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484649678 : ℝ) ≤ plow 12295 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.882821031934 : ℝ) ≤ √12295 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284467615279 : ℝ) / (2 * 0.560484649678 * 110.882821031934)) * 0.163919700024 +
        0.284467615279 ^ 2 / (2 * 0.560484649678 * 110.882821031934) := by gcongr
    _ ≤ (0.164945890939 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414806291) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427914825)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284467615279) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12295 12295 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484649678 : ℝ) ≤ plow 12295 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.882821031934 : ℝ) ≤ √12295 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12295 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12295 Θ 1.22 ≤ 0.011959476569 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.882821031934 := by gcongr <;> linarith
      _ ≤ (0.011959476569 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12295 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12295 12295 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12295 12295 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12295 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12295 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12295 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12295 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164945890939 + 0.011959476569 + (0.008646 : ℝ) *
        (1 + 2 * (0.284467615279 + 0.011959476569) / (0.560484649678 * 110.882821031934))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12295]

end BstLean.Part264b.N12295

/-! The original eight local profiles supply actual 12295 moment certificates. -/
namespace BstLean.Part264b.N12295
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12295 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053414806291 ∧
    0 ≤ bN 12295 BstLean.Part154.csC (groupTheta g) ∧ bN 12295 BstLean.Part154.csC (groupTheta g) ≤ 0.001427914825 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12295 12295 0.011
      (momentAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12295 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12295 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12295 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231116434490 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12295 0.011
      (momentAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12295 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12295
/-! The actual computed-centre upper energy formula at 12295. -/
namespace BstLean.Part264b.N12295
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12295

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12295
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12295 cell12295)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086774185066
  | 2 => 0.087743019677
  | 3 => 0.088714186253
  | 4 => 0.089690036700
  | 5 => 0.090673379380
  | 6 => 0.091667542000
  | 7 => 0.092676439551
  | 8 => 0.093704647192
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12295 12295 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12295 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12295

/-! Actual upper energy certificates on all 43 source endpoints at 12295. -/
namespace BstLean.Part264b.N12295
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12295 cell12295)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12295 (gMinus 12295) (1 - (cell12295 i).lower) ≤ 1 ∧
    energyUpper 12295 (gMinus 12295) (BstLean.Part211.gPlus 12295)
      (finiteEnergy 12295 12295 0.011) (1 - (cell12295 i).lower) ≤
      (cell12295 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12295) (by norm_num)
        (q := 1 - (cell12295 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12295,cell12295]) (by norm_num [scalarRow12295,cell12295])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12295,cell12295])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12295

/-! Source-cell containment and simple scalar guards at 12295. -/
namespace BstLean.Part264b.N12295
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12295 cell12295)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12295 ⟨10,by decide⟩).lower ∧ (cell12295 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12295 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12295 ⟨11,by decide⟩).lower ∧ (cell12295 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12295 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12295 ⟨12,by decide⟩).lower ∧ (cell12295 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12295 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12295 ⟨13,by decide⟩).lower ∧ (cell12295 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12295 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12295 ⟨14,by decide⟩).lower ∧ (cell12295 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12295 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12295 ⟨15,by decide⟩).lower ∧ (cell12295 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12295 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12295 ⟨16,by decide⟩).lower ∧ (cell12295 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12295 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12295 ⟨17,by decide⟩).lower ∧ (cell12295 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12295 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12295 ⟨18,by decide⟩).lower ∧ (cell12295 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12295 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12295 ⟨19,by decide⟩).lower ∧ (cell12295 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12295 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12295 ⟨20,by decide⟩).lower ∧ (cell12295 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12295 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12295 ⟨21,by decide⟩).lower ∧ (cell12295 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12295 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12295 ⟨22,by decide⟩).lower ∧ (cell12295 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12295 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12295 ⟨23,by decide⟩).lower ∧ (cell12295 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12295 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12295 ⟨24,by decide⟩).lower ∧ (cell12295 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12295 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12295 ⟨25,by decide⟩).lower ∧ (cell12295 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12295 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12295 ⟨26,by decide⟩).lower ∧ (cell12295 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12295 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12295 ⟨27,by decide⟩).lower ∧ (cell12295 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12295 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12295 ⟨28,by decide⟩).lower ∧ (cell12295 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12295 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12295 ⟨29,by decide⟩).lower ∧ (cell12295 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12295 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12295 ⟨30,by decide⟩).lower ∧ (cell12295 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12295 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12295 ⟨31,by decide⟩).lower ∧ (cell12295 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12295 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12295 ⟨32,by decide⟩).lower ∧ (cell12295 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12295 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12295 ⟨33,by decide⟩).lower ∧ (cell12295 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12295 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12295 ⟨34,by decide⟩).lower ∧ (cell12295 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12295 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12295 ⟨35,by decide⟩).lower ∧ (cell12295 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12295 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12295 ⟨36,by decide⟩).lower ∧ (cell12295 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12295 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12295 ⟨37,by decide⟩).lower ∧ (cell12295 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12295 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12295 ⟨38,by decide⟩).lower ∧ (cell12295 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12295 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12295 ⟨39,by decide⟩).lower ∧ (cell12295 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12295 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12295 ⟨40,by decide⟩).lower ∧ (cell12295 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12295 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12295 ⟨41,by decide⟩).lower ∧ (cell12295 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12295 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12295 ⟨42,by decide⟩).lower ∧ (cell12295 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12295 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12295 ⟨43,by decide⟩).lower ∧ (cell12295 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12295 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12295 ⟨44,by decide⟩).lower ∧ (cell12295 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12295 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12295 ⟨45,by decide⟩).lower ∧ (cell12295 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12295 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12295 ⟨46,by decide⟩).lower ∧ (cell12295 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12295 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12295 ⟨47,by decide⟩).lower ∧ (cell12295 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12295 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12295 ⟨48,by decide⟩).lower ∧ (cell12295 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12295 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12295 ⟨49,by decide⟩).lower ∧ (cell12295 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12295 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12295 ⟨50,by decide⟩).lower ∧ (cell12295 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12295 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12295 ⟨51,by decide⟩).lower ∧ (cell12295 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12295 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12295 ⟨52,by decide⟩).lower ∧ (cell12295 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12295 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12295 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12295 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12295,cell12295,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12295 i).lower ∧
    (cell12295 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12295 i).upper ≤ (0.532 : ℝ) ∧
    (cell12295 i).centre ≤ (0.1 : ℝ) ∧ (cell12295 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12295 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12295 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12295

/-! The local source numeric instances at 12295 have no network premises. -/
namespace BstLean.Part264b.N12295
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12295 cell12295)

noncomputable def sourceNumerics12295 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12295 (cell12295 i)
      scalarRow12295.M scalarRow12295.H scalarRow12295.xi := by
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
    energy_allowance := scalarRow12295.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12295]
    centre_nonneg := (scalarRow12295.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12295]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12295
/-! Actual 12296 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12296
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12296 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12296 12296 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12296.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12296 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12296 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12296 := gPlus_lower 12296
end BstLean.Part264b.N12296

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12296
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036397960378 : ℝ) ≤ wn 12296 := by
  have hn : √(12296 : ℝ) ≤ 110.887330205033 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12296 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.887330205033 ≤ 2 / √12296 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260304590 : ℝ) ≤ rhoBar 12296 BstLean.Part154.csC ∧
    rhoBar 12296 BstLean.Part154.csC ≤ 0.000260331877 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036397960378 : ℝ) / (1.295212 * 12296) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12296) := by gcongr
      _ ≤ (0.000260331877 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12296 BstLean.Part154.csC) ≤ 0.001041395281 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12296 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12296 BstLean.Part154.csC) (piBar (rhoBar 12296 BstLean.Part154.csC)) ≤ 0.000198843554 ∧
    cc1 (rhoBar 12296 BstLean.Part154.csC) (piBar (rhoBar 12296 BstLean.Part154.csC)) ≤ 0.000126525410 ∧
    cc2 (rhoBar 12296 BstLean.Part154.csC) ≤ 0.000073448892 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12296 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12296 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12296 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12296 BstLean.Part154.csC * nuR (rhoBar 12296 BstLean.Part154.csC)) ≤ 0.000520680697 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260331877 : ℝ) * 0.001041395281 := by gcongr
      _ ≤ (0.000520680697 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12296 BstLean.Part154.csC) * nuR (rhoBar 12296 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041395281 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12296 BstLean.Part154.csC) * rhoBar 12296 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260331877 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260331877 / 2 + 0.399 * 0.001041395281 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198843554 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520680697 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126525410 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260331877 / 1.414213562 := by gcongr
      _ ≤ (0.000073448892 : ℝ) := by norm_num

end BstLean.Part264b.N12296

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12296
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12296 BstLean.Part154.csC) (piBar (rhoBar 12296 BstLean.Part154.csC)) ≤ 1.70749E-7 := by
  have hr0 : 0 ≤ rhoBar 12296 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12296 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12296 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12296 BstLean.Part154.csC) (piBar (rhoBar 12296 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12296 BstLean.Part154.csC) (piBar (rhoBar 12296 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12296 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198843554 : ℝ) ^ 2 + 0.000126525410 ^ 2 + 3 * 0.000073448892 ^ 2 +
        2 * 0.797885 * 0.000198843554 * 0.000126525410 + 2 * 0.000198843554 * 0.000073448892 +
        4 * 0.797885 * 0.000126525410 * 0.000073448892 := by gcongr
    _ ≤ (1.70749E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12296 BstLean.Part154.csC Θ ≤ 0.002719616927 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12296 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12296 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12296 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12296 BstLean.Part154.csC) (piBar (rhoBar 12296 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12296 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70749E-7 / (0.000260304590 : ℝ) := by gcongr
    _ ≤ 0.002719616927 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12296 BstLean.Part154.csC Θ ≤ 0.003019273247 + 0.000687130073 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12296 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12296 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12296 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260331877 +
        (6863 / 10000) * 0.000260331877 * 12296 * 0.001041395281) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003019273247 + 0.000687130073 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12296 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12296 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12296 0.011 Θ ∧ gammaRatio 12296 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12296 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12296) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12296 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12296 0.011 Θ) :=
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
    badAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12296 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12296 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12296 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12296 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12296 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12296 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12296 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12296 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12296 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12296 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12296 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004119273247 + 0.003406747000 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12296

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12296
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12296 BstLean.Part154.csC) (piBar (rhoBar 12296 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12296 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12296 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12296 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12296 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12296 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12296 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12296 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12296 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12296 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12296 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12296 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12296 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053348987388 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12296) ≤ 0.010769828969 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12296 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010769828969 + 2 * 0.737676 / 12296) := by gcongr
    _ ≤ (0.053348987388 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12296 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12296

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12296
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484697926 : ℝ) ≤ plow 12296 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12296) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414415422)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427798887) : eMP 12296 0.011 xi bn ≤ 0.001228469293 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12296 : ℝ) * (1 - 0.011))) ≤ 0.000607335136 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001427798887 / (12296 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607335136 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607335136 : ℝ) + 3.141593 * 0.053414415422 / (12296 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001228469293 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414415422)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427798887) : PiBarMP 12296 12 0.011 xi bn ≤ 0.163913029401 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12296 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037786226155 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.275763429685 : ℝ) ≤ √((12296 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.887330205032 : ℝ) ≤ √12296 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12296) ≤ 0.125644726382 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037786226155 + 0.053414415422 * 1.772454 / (2 * (110.275763429685 : ℝ))) * (1 + 0.001228469293) +
        8 / (12296 * 110.887330205032) + 0.125644726382 := by gcongr
    _ ≤ (0.163913029401 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414415422)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427798887) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284464576266) :
    parallelOracle 12296 0.011 xi bn cd ≤ 0.164939145315 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12296 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12296 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484697926 : ℝ) ≤ plow 12296 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.887330205032 : ℝ) ≤ √12296 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284464576266 : ℝ) / (2 * 0.560484697926 * 110.887330205032)) * 0.163913029401 +
        0.284464576266 ^ 2 / (2 * 0.560484697926 * 110.887330205032) := by gcongr
    _ ≤ (0.164939145315 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414415422) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427798887)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284464576266) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12296 12296 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484697926 : ℝ) ≤ plow 12296 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.887330205032 : ℝ) ≤ √12296 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12296 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12296 Θ 1.22 ≤ 0.011958990244 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.887330205032 := by gcongr <;> linarith
      _ ≤ (0.011958990244 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12296 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12296 12296 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12296 12296 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12296 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12296 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12296 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12296 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164939145315 + 0.011958990244 + (0.008646 : ℝ) *
        (1 + 2 * (0.284464576266 + 0.011958990244) / (0.560484697926 * 110.887330205032))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12296]

end BstLean.Part264b.N12296

/-! The original eight local profiles supply actual 12296 moment certificates. -/
namespace BstLean.Part264b.N12296
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12296 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053414415422 ∧
    0 ≤ bN 12296 BstLean.Part154.csC (groupTheta g) ∧ bN 12296 BstLean.Part154.csC (groupTheta g) ≤ 0.001427798887 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12296 12296 0.011
      (momentAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12296 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12296 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12296 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231115588878 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12296 0.011
      (momentAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12296 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12296
/-! The actual computed-centre upper energy formula at 12296. -/
namespace BstLean.Part264b.N12296
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12296

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12296
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12296 cell12296)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086770722505
  | 2 => 0.087739479824
  | 3 => 0.088710555756
  | 4 => 0.089686299313
  | 5 => 0.090669515486
  | 6 => 0.091663528080
  | 7 => 0.092672247592
  | 8 => 0.093700244046
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12296 12296 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12296 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12296

/-! Actual upper energy certificates on all 43 source endpoints at 12296. -/
namespace BstLean.Part264b.N12296
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12296 cell12296)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12296 (gMinus 12296) (1 - (cell12296 i).lower) ≤ 1 ∧
    energyUpper 12296 (gMinus 12296) (BstLean.Part211.gPlus 12296)
      (finiteEnergy 12296 12296 0.011) (1 - (cell12296 i).lower) ≤
      (cell12296 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12296) (by norm_num)
        (q := 1 - (cell12296 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12296,cell12296]) (by norm_num [scalarRow12296,cell12296])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12296,cell12296])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12296

/-! Source-cell containment and simple scalar guards at 12296. -/
namespace BstLean.Part264b.N12296
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12296 cell12296)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12296 ⟨10,by decide⟩).lower ∧ (cell12296 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12296 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12296 ⟨11,by decide⟩).lower ∧ (cell12296 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12296 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12296 ⟨12,by decide⟩).lower ∧ (cell12296 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12296 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12296 ⟨13,by decide⟩).lower ∧ (cell12296 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12296 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12296 ⟨14,by decide⟩).lower ∧ (cell12296 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12296 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12296 ⟨15,by decide⟩).lower ∧ (cell12296 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12296 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12296 ⟨16,by decide⟩).lower ∧ (cell12296 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12296 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12296 ⟨17,by decide⟩).lower ∧ (cell12296 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12296 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12296 ⟨18,by decide⟩).lower ∧ (cell12296 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12296 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12296 ⟨19,by decide⟩).lower ∧ (cell12296 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12296 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12296 ⟨20,by decide⟩).lower ∧ (cell12296 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12296 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12296 ⟨21,by decide⟩).lower ∧ (cell12296 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12296 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12296 ⟨22,by decide⟩).lower ∧ (cell12296 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12296 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12296 ⟨23,by decide⟩).lower ∧ (cell12296 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12296 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12296 ⟨24,by decide⟩).lower ∧ (cell12296 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12296 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12296 ⟨25,by decide⟩).lower ∧ (cell12296 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12296 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12296 ⟨26,by decide⟩).lower ∧ (cell12296 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12296 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12296 ⟨27,by decide⟩).lower ∧ (cell12296 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12296 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12296 ⟨28,by decide⟩).lower ∧ (cell12296 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12296 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12296 ⟨29,by decide⟩).lower ∧ (cell12296 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12296 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12296 ⟨30,by decide⟩).lower ∧ (cell12296 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12296 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12296 ⟨31,by decide⟩).lower ∧ (cell12296 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12296 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12296 ⟨32,by decide⟩).lower ∧ (cell12296 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12296 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12296 ⟨33,by decide⟩).lower ∧ (cell12296 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12296 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12296 ⟨34,by decide⟩).lower ∧ (cell12296 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12296 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12296 ⟨35,by decide⟩).lower ∧ (cell12296 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12296 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12296 ⟨36,by decide⟩).lower ∧ (cell12296 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12296 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12296 ⟨37,by decide⟩).lower ∧ (cell12296 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12296 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12296 ⟨38,by decide⟩).lower ∧ (cell12296 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12296 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12296 ⟨39,by decide⟩).lower ∧ (cell12296 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12296 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12296 ⟨40,by decide⟩).lower ∧ (cell12296 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12296 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12296 ⟨41,by decide⟩).lower ∧ (cell12296 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12296 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12296 ⟨42,by decide⟩).lower ∧ (cell12296 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12296 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12296 ⟨43,by decide⟩).lower ∧ (cell12296 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12296 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12296 ⟨44,by decide⟩).lower ∧ (cell12296 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12296 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12296 ⟨45,by decide⟩).lower ∧ (cell12296 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12296 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12296 ⟨46,by decide⟩).lower ∧ (cell12296 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12296 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12296 ⟨47,by decide⟩).lower ∧ (cell12296 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12296 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12296 ⟨48,by decide⟩).lower ∧ (cell12296 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12296 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12296 ⟨49,by decide⟩).lower ∧ (cell12296 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12296 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12296 ⟨50,by decide⟩).lower ∧ (cell12296 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12296 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12296 ⟨51,by decide⟩).lower ∧ (cell12296 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12296 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12296 ⟨52,by decide⟩).lower ∧ (cell12296 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12296 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12296 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12296 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12296,cell12296,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12296 i).lower ∧
    (cell12296 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12296 i).upper ≤ (0.532 : ℝ) ∧
    (cell12296 i).centre ≤ (0.1 : ℝ) ∧ (cell12296 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12296 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12296 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12296

/-! The local source numeric instances at 12296 have no network premises. -/
namespace BstLean.Part264b.N12296
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12296 cell12296)

noncomputable def sourceNumerics12296 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12296 (cell12296 i)
      scalarRow12296.M scalarRow12296.H scalarRow12296.xi := by
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
    energy_allowance := scalarRow12296.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12296]
    centre_nonneg := (scalarRow12296.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12296]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12296
/-! Actual 12297 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12297
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12297 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12297 12297 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12297.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12297 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12297 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12297 := gPlus_lower 12297
end BstLean.Part264b.N12297

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12297
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036396467169 : ℝ) ≤ wn 12297 := by
  have hn : √(12297 : ℝ) ≤ 110.891839194776 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12297 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.891839194776 ≤ 2 / √12297 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260283047 : ℝ) ≤ rhoBar 12297 BstLean.Part154.csC ∧
    rhoBar 12297 BstLean.Part154.csC ≤ 0.000260310707 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036396467169 : ℝ) / (1.295212 * 12297) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12297) := by gcongr
      _ ≤ (0.000260310707 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12297 BstLean.Part154.csC) ≤ 0.001041310590 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12297 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12297 BstLean.Part154.csC) (piBar (rhoBar 12297 BstLean.Part154.csC)) ≤ 0.000198827384 ∧
    cc1 (rhoBar 12297 BstLean.Part154.csC) (piBar (rhoBar 12297 BstLean.Part154.csC)) ≤ 0.000126515121 ∧
    cc2 (rhoBar 12297 BstLean.Part154.csC) ≤ 0.000073442920 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12297 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12297 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12297 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12297 BstLean.Part154.csC * nuR (rhoBar 12297 BstLean.Part154.csC)) ≤ 0.000520638355 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260310707 : ℝ) * 0.001041310590 := by gcongr
      _ ≤ (0.000520638355 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12297 BstLean.Part154.csC) * nuR (rhoBar 12297 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041310590 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12297 BstLean.Part154.csC) * rhoBar 12297 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260310707 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260310707 / 2 + 0.399 * 0.001041310590 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198827384 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520638355 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126515121 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260310707 / 1.414213562 := by gcongr
      _ ≤ (0.000073442920 : ℝ) := by norm_num

end BstLean.Part264b.N12297

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12297
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12297 BstLean.Part154.csC) (piBar (rhoBar 12297 BstLean.Part154.csC)) ≤ 1.70721E-7 := by
  have hr0 : 0 ≤ rhoBar 12297 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12297 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12297 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12297 BstLean.Part154.csC) (piBar (rhoBar 12297 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12297 BstLean.Part154.csC) (piBar (rhoBar 12297 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12297 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198827384 : ℝ) ^ 2 + 0.000126515121 ^ 2 + 3 * 0.000073442920 ^ 2 +
        2 * 0.797885 * 0.000198827384 * 0.000126515121 + 2 * 0.000198827384 * 0.000073442920 +
        4 * 0.797885 * 0.000126515121 * 0.000073442920 := by gcongr
    _ ≤ (1.70721E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12297 BstLean.Part154.csC Θ ≤ 0.002719396014 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12297 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12297 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12297 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12297 BstLean.Part154.csC) (piBar (rhoBar 12297 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12297 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70721E-7 / (0.000260283047 : ℝ) := by gcongr
    _ ≤ 0.002719396014 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12297 BstLean.Part154.csC Θ ≤ 0.003019027710 + 0.000687074196 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12297 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12297 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12297 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260310707 +
        (6863 / 10000) * 0.000260310707 * 12297 * 0.001041310590) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003019027710 + 0.000687074196 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12297 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12297 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12297 0.011 Θ ∧ gammaRatio 12297 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12297 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12297) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12297 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12297 0.011 Θ) :=
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
    badAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12297 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12297 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12297 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12297 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12297 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12297 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12297 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12297 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12297 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12297 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12297 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004119027710 + 0.003406470210 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12297

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12297
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12297 BstLean.Part154.csC) (piBar (rhoBar 12297 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12297 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12297 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12297 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12297 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12297 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12297 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12297 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12297 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12297 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12297 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12297 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12297 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053346794255 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12297) ≤ 0.010769391055 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12297 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010769391055 + 2 * 0.737676 / 12297) := by gcongr
    _ ≤ (0.053346794255 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12297 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12297

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12297
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484746165 : ℝ) ≤ plow 12297 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12297) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414024571)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427682908) : eMP 12297 0.011 xi bn ≤ 0.001228369348 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12297 : ℝ) * (1 - 0.011))) ≤ 0.000607285775 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001427682908 / (12297 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607285775 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607285775 : ℝ) + 3.141593 * 0.053414024571 / (12297 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001228369348 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414024571)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427682908) : PiBarMP 12297 12 0.011 xi bn ≤ 0.163906358797 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12297 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037784691451 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.280247551408 : ℝ) ≤ √((12297 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.891839194775 : ℝ) ≤ √12297 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12297) ≤ 0.125639617523 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037784691451 + 0.053414024571 * 1.772454 / (2 * (110.280247551408 : ℝ))) * (1 + 0.001228369348) +
        8 / (12297 * 110.891839194775) + 0.125639617523 := by gcongr
    _ ≤ (0.163906358797 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414024571)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427682908) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284461537556) :
    parallelOracle 12297 0.011 xi bn cd ≤ 0.164932399720 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12297 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12297 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484746165 : ℝ) ≤ plow 12297 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.891839194775 : ℝ) ≤ √12297 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284461537556 : ℝ) / (2 * 0.560484746165 * 110.891839194775)) * 0.163906358797 +
        0.284461537556 ^ 2 / (2 * 0.560484746165 * 110.891839194775) := by gcongr
    _ ≤ (0.164932399720 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053414024571) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427682908)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284461537556) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12297 12297 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484746165 : ℝ) ≤ plow 12297 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.891839194775 : ℝ) ≤ √12297 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12297 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12297 Θ 1.22 ≤ 0.011958503977 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.891839194775 := by gcongr <;> linarith
      _ ≤ (0.011958503977 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12297 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12297 12297 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12297 12297 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12297 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12297 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12297 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12297 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164932399720 + 0.011958503977 + (0.008646 : ℝ) *
        (1 + 2 * (0.284461537556 + 0.011958503977) / (0.560484746165 * 110.891839194775))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12297]

end BstLean.Part264b.N12297

/-! The original eight local profiles supply actual 12297 moment certificates. -/
namespace BstLean.Part264b.N12297
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12297 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053414024571 ∧
    0 ≤ bN 12297 BstLean.Part154.csC (groupTheta g) ∧ bN 12297 BstLean.Part154.csC (groupTheta g) ≤ 0.001427682908 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12297 12297 0.011
      (momentAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12297 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12297 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12297 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231114743301 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12297 0.011
      (momentAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12297 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12297
/-! The actual computed-centre upper energy formula at 12297. -/
namespace BstLean.Part264b.N12297
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12297

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12297
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12297 cell12297)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086767261611
  | 2 => 0.087735941714
  | 3 => 0.088706927094
  | 4 => 0.089682563875
  | 5 => 0.090665653681
  | 6 => 0.091659516415
  | 7 => 0.092668058090
  | 8 => 0.093695843598
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12297 12297 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12297 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12297

/-! Actual upper energy certificates on all 43 source endpoints at 12297. -/
namespace BstLean.Part264b.N12297
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12297 cell12297)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12297 (gMinus 12297) (1 - (cell12297 i).lower) ≤ 1 ∧
    energyUpper 12297 (gMinus 12297) (BstLean.Part211.gPlus 12297)
      (finiteEnergy 12297 12297 0.011) (1 - (cell12297 i).lower) ≤
      (cell12297 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12297) (by norm_num)
        (q := 1 - (cell12297 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12297,cell12297]) (by norm_num [scalarRow12297,cell12297])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12297,cell12297])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12297

/-! Source-cell containment and simple scalar guards at 12297. -/
namespace BstLean.Part264b.N12297
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12297 cell12297)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12297 ⟨10,by decide⟩).lower ∧ (cell12297 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12297 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12297 ⟨11,by decide⟩).lower ∧ (cell12297 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12297 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12297 ⟨12,by decide⟩).lower ∧ (cell12297 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12297 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12297 ⟨13,by decide⟩).lower ∧ (cell12297 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12297 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12297 ⟨14,by decide⟩).lower ∧ (cell12297 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12297 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12297 ⟨15,by decide⟩).lower ∧ (cell12297 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12297 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12297 ⟨16,by decide⟩).lower ∧ (cell12297 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12297 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12297 ⟨17,by decide⟩).lower ∧ (cell12297 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12297 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12297 ⟨18,by decide⟩).lower ∧ (cell12297 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12297 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12297 ⟨19,by decide⟩).lower ∧ (cell12297 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12297 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12297 ⟨20,by decide⟩).lower ∧ (cell12297 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12297 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12297 ⟨21,by decide⟩).lower ∧ (cell12297 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12297 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12297 ⟨22,by decide⟩).lower ∧ (cell12297 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12297 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12297 ⟨23,by decide⟩).lower ∧ (cell12297 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12297 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12297 ⟨24,by decide⟩).lower ∧ (cell12297 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12297 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12297 ⟨25,by decide⟩).lower ∧ (cell12297 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12297 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12297 ⟨26,by decide⟩).lower ∧ (cell12297 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12297 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12297 ⟨27,by decide⟩).lower ∧ (cell12297 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12297 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12297 ⟨28,by decide⟩).lower ∧ (cell12297 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12297 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12297 ⟨29,by decide⟩).lower ∧ (cell12297 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12297 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12297 ⟨30,by decide⟩).lower ∧ (cell12297 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12297 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12297 ⟨31,by decide⟩).lower ∧ (cell12297 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12297 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12297 ⟨32,by decide⟩).lower ∧ (cell12297 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12297 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12297 ⟨33,by decide⟩).lower ∧ (cell12297 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12297 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12297 ⟨34,by decide⟩).lower ∧ (cell12297 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12297 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12297 ⟨35,by decide⟩).lower ∧ (cell12297 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12297 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12297 ⟨36,by decide⟩).lower ∧ (cell12297 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12297 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12297 ⟨37,by decide⟩).lower ∧ (cell12297 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12297 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12297 ⟨38,by decide⟩).lower ∧ (cell12297 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12297 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12297 ⟨39,by decide⟩).lower ∧ (cell12297 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12297 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12297 ⟨40,by decide⟩).lower ∧ (cell12297 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12297 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12297 ⟨41,by decide⟩).lower ∧ (cell12297 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12297 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12297 ⟨42,by decide⟩).lower ∧ (cell12297 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12297 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12297 ⟨43,by decide⟩).lower ∧ (cell12297 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12297 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12297 ⟨44,by decide⟩).lower ∧ (cell12297 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12297 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12297 ⟨45,by decide⟩).lower ∧ (cell12297 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12297 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12297 ⟨46,by decide⟩).lower ∧ (cell12297 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12297 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12297 ⟨47,by decide⟩).lower ∧ (cell12297 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12297 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12297 ⟨48,by decide⟩).lower ∧ (cell12297 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12297 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12297 ⟨49,by decide⟩).lower ∧ (cell12297 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12297 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12297 ⟨50,by decide⟩).lower ∧ (cell12297 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12297 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12297 ⟨51,by decide⟩).lower ∧ (cell12297 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12297 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12297 ⟨52,by decide⟩).lower ∧ (cell12297 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12297 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12297 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12297 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12297,cell12297,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12297 i).lower ∧
    (cell12297 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12297 i).upper ≤ (0.532 : ℝ) ∧
    (cell12297 i).centre ≤ (0.1 : ℝ) ∧ (cell12297 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12297 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12297 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12297

/-! The local source numeric instances at 12297 have no network premises. -/
namespace BstLean.Part264b.N12297
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12297 cell12297)

noncomputable def sourceNumerics12297 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12297 (cell12297 i)
      scalarRow12297.M scalarRow12297.H scalarRow12297.xi := by
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
    energy_allowance := scalarRow12297.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12297]
    centre_nonneg := (scalarRow12297.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12297]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12297
/-! Actual 12298 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12298
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12298 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12298 12298 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12298.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12298 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12298 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12298 := gPlus_lower 12298
end BstLean.Part264b.N12298

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12298
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036394974142 : ℝ) ≤ wn 12298 := by
  have hn : √(12298 : ℝ) ≤ 110.896348001186 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12298 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.896348001186 ≤ 2 / √12298 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260261507 : ℝ) ≤ rhoBar 12298 BstLean.Part154.csC ∧
    rhoBar 12298 BstLean.Part154.csC ≤ 0.000260289540 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036394974142 : ℝ) / (1.295212 * 12298) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12298) := by gcongr
      _ ≤ (0.000260289540 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12298 BstLean.Part154.csC) ≤ 0.001041225911 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12298 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12298 BstLean.Part154.csC) (piBar (rhoBar 12298 BstLean.Part154.csC)) ≤ 0.000198811215 ∧
    cc1 (rhoBar 12298 BstLean.Part154.csC) (piBar (rhoBar 12298 BstLean.Part154.csC)) ≤ 0.000126504833 ∧
    cc2 (rhoBar 12298 BstLean.Part154.csC) ≤ 0.000073436948 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12298 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12298 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12298 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12298 BstLean.Part154.csC * nuR (rhoBar 12298 BstLean.Part154.csC)) ≤ 0.000520596018 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260289540 : ℝ) * 0.001041225911 := by gcongr
      _ ≤ (0.000520596018 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12298 BstLean.Part154.csC) * nuR (rhoBar 12298 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041225911 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12298 BstLean.Part154.csC) * rhoBar 12298 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260289540 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260289540 / 2 + 0.399 * 0.001041225911 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198811215 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520596018 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126504833 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260289540 / 1.414213562 := by gcongr
      _ ≤ (0.000073436948 : ℝ) := by norm_num

end BstLean.Part264b.N12298

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12298
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12298 BstLean.Part154.csC) (piBar (rhoBar 12298 BstLean.Part154.csC)) ≤ 1.70693E-7 := by
  have hr0 : 0 ≤ rhoBar 12298 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12298 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12298 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12298 BstLean.Part154.csC) (piBar (rhoBar 12298 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12298 BstLean.Part154.csC) (piBar (rhoBar 12298 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12298 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198811215 : ℝ) ^ 2 + 0.000126504833 ^ 2 + 3 * 0.000073436948 ^ 2 +
        2 * 0.797885 * 0.000198811215 * 0.000126504833 + 2 * 0.000198811215 * 0.000073436948 +
        4 * 0.797885 * 0.000126504833 * 0.000073436948 := by gcongr
    _ ≤ (1.70693E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12298 BstLean.Part154.csC Θ ≤ 0.002719175033 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12298 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12298 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12298 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12298 BstLean.Part154.csC) (piBar (rhoBar 12298 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12298 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70693E-7 / (0.000260261507 : ℝ) := by gcongr
    _ ≤ 0.002719175033 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12298 BstLean.Part154.csC Θ ≤ 0.003018782203 + 0.000687018327 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12298 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12298 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12298 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260289540 +
        (6863 / 10000) * 0.000260289540 * 12298 * 0.001041225911) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003018782203 + 0.000687018327 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12298 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12298 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12298 0.011 Θ ∧ gammaRatio 12298 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12298 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12298) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12298 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12298 0.011 Θ) :=
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
    badAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12298 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12298 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12298 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12298 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12298 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12298 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12298 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12298 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12298 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12298 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12298 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004118782203 + 0.003406193360 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12298

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12298
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12298 BstLean.Part154.csC) (piBar (rhoBar 12298 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12298 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12298 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12298 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12298 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12298 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12298 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12298 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12298 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12298 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12298 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12298 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12298 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053344601395 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12298) ≤ 0.010768953195 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12298 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010768953195 + 2 * 0.737676 / 12298) := by gcongr
    _ ≤ (0.053344601395 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12298 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12298

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12298
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484794397 : ℝ) ≤ plow 12298 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12298) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053413633717)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427566893) : eMP 12298 0.011 xi bn ≤ 0.001228269395 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12298 : ℝ) * (1 - 0.011))) ≤ 0.000607236410 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001427566893 / (12298 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607236410 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607236410 : ℝ) + 3.141593 * 0.053413633717 / (12298 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001228269395 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053413633717)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427566893) : PiBarMP 12298 12 0.011 xi bn ≤ 0.163899688279 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12298 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037783156208 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.284731490809 : ℝ) ≤ √((12298 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.896348001185 : ℝ) ≤ √12298 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12298) ≤ 0.125634509287 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037783156208 + 0.053413633717 * 1.772454 / (2 * (110.284731490809 : ℝ))) * (1 + 0.001228269395) +
        8 / (12298 * 110.896348001185) + 0.125634509287 := by gcongr
    _ ≤ (0.163899688279 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053413633717)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427566893) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284458499110) :
    parallelOracle 12298 0.011 xi bn cd ≤ 0.164925654221 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12298 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12298 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484794397 : ℝ) ≤ plow 12298 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.896348001185 : ℝ) ≤ √12298 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284458499110 : ℝ) / (2 * 0.560484794397 * 110.896348001185)) * 0.163899688279 +
        0.284458499110 ^ 2 / (2 * 0.560484794397 * 110.896348001185) := by gcongr
    _ ≤ (0.164925654221 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053413633717) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427566893)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284458499110) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12298 12298 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484794397 : ℝ) ≤ plow 12298 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.896348001185 : ℝ) ≤ √12298 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12298 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12298 Θ 1.22 ≤ 0.011958017770 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.896348001185 := by gcongr <;> linarith
      _ ≤ (0.011958017770 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12298 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12298 12298 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12298 12298 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12298 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12298 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12298 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12298 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164925654221 + 0.011958017770 + (0.008646 : ℝ) *
        (1 + 2 * (0.284458499110 + 0.011958017770) / (0.560484794397 * 110.896348001185))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12298]

end BstLean.Part264b.N12298

/-! The original eight local profiles supply actual 12298 moment certificates. -/
namespace BstLean.Part264b.N12298
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12298 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053413633717 ∧
    0 ≤ bN 12298 BstLean.Part154.csC (groupTheta g) ∧ bN 12298 BstLean.Part154.csC (groupTheta g) ≤ 0.001427566893 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12298 12298 0.011
      (momentAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12298 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12298 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12298 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231113897715 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12298 0.011
      (momentAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12298 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12298
/-! The actual computed-centre upper energy formula at 12298. -/
namespace BstLean.Part264b.N12298
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12298

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12298
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12298 cell12298)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086763802382
  | 2 => 0.087732405344
  | 3 => 0.088703300266
  | 4 => 0.089678830385
  | 5 => 0.090661793961
  | 6 => 0.091655507003
  | 7 => 0.092663871043
  | 8 => 0.093691445846
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12298 12298 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12298 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12298

/-! Actual upper energy certificates on all 43 source endpoints at 12298. -/
namespace BstLean.Part264b.N12298
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12298 cell12298)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12298 (gMinus 12298) (1 - (cell12298 i).lower) ≤ 1 ∧
    energyUpper 12298 (gMinus 12298) (BstLean.Part211.gPlus 12298)
      (finiteEnergy 12298 12298 0.011) (1 - (cell12298 i).lower) ≤
      (cell12298 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12298) (by norm_num)
        (q := 1 - (cell12298 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12298,cell12298]) (by norm_num [scalarRow12298,cell12298])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12298,cell12298])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12298

/-! Source-cell containment and simple scalar guards at 12298. -/
namespace BstLean.Part264b.N12298
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12298 cell12298)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12298 ⟨10,by decide⟩).lower ∧ (cell12298 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12298 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12298 ⟨11,by decide⟩).lower ∧ (cell12298 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12298 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12298 ⟨12,by decide⟩).lower ∧ (cell12298 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12298 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12298 ⟨13,by decide⟩).lower ∧ (cell12298 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12298 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12298 ⟨14,by decide⟩).lower ∧ (cell12298 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12298 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12298 ⟨15,by decide⟩).lower ∧ (cell12298 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12298 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12298 ⟨16,by decide⟩).lower ∧ (cell12298 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12298 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12298 ⟨17,by decide⟩).lower ∧ (cell12298 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12298 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12298 ⟨18,by decide⟩).lower ∧ (cell12298 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12298 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12298 ⟨19,by decide⟩).lower ∧ (cell12298 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12298 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12298 ⟨20,by decide⟩).lower ∧ (cell12298 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12298 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12298 ⟨21,by decide⟩).lower ∧ (cell12298 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12298 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12298 ⟨22,by decide⟩).lower ∧ (cell12298 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12298 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12298 ⟨23,by decide⟩).lower ∧ (cell12298 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12298 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12298 ⟨24,by decide⟩).lower ∧ (cell12298 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12298 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12298 ⟨25,by decide⟩).lower ∧ (cell12298 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12298 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12298 ⟨26,by decide⟩).lower ∧ (cell12298 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12298 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12298 ⟨27,by decide⟩).lower ∧ (cell12298 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12298 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12298 ⟨28,by decide⟩).lower ∧ (cell12298 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12298 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12298 ⟨29,by decide⟩).lower ∧ (cell12298 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12298 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12298 ⟨30,by decide⟩).lower ∧ (cell12298 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12298 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12298 ⟨31,by decide⟩).lower ∧ (cell12298 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12298 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12298 ⟨32,by decide⟩).lower ∧ (cell12298 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12298 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12298 ⟨33,by decide⟩).lower ∧ (cell12298 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12298 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12298 ⟨34,by decide⟩).lower ∧ (cell12298 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12298 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12298 ⟨35,by decide⟩).lower ∧ (cell12298 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12298 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12298 ⟨36,by decide⟩).lower ∧ (cell12298 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12298 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12298 ⟨37,by decide⟩).lower ∧ (cell12298 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12298 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12298 ⟨38,by decide⟩).lower ∧ (cell12298 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12298 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12298 ⟨39,by decide⟩).lower ∧ (cell12298 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12298 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12298 ⟨40,by decide⟩).lower ∧ (cell12298 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12298 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12298 ⟨41,by decide⟩).lower ∧ (cell12298 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12298 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12298 ⟨42,by decide⟩).lower ∧ (cell12298 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12298 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12298 ⟨43,by decide⟩).lower ∧ (cell12298 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12298 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12298 ⟨44,by decide⟩).lower ∧ (cell12298 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12298 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12298 ⟨45,by decide⟩).lower ∧ (cell12298 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12298 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12298 ⟨46,by decide⟩).lower ∧ (cell12298 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12298 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12298 ⟨47,by decide⟩).lower ∧ (cell12298 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12298 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12298 ⟨48,by decide⟩).lower ∧ (cell12298 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12298 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12298 ⟨49,by decide⟩).lower ∧ (cell12298 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12298 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12298 ⟨50,by decide⟩).lower ∧ (cell12298 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12298 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12298 ⟨51,by decide⟩).lower ∧ (cell12298 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12298 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12298 ⟨52,by decide⟩).lower ∧ (cell12298 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12298 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12298 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12298 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12298,cell12298,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12298 i).lower ∧
    (cell12298 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12298 i).upper ≤ (0.532 : ℝ) ∧
    (cell12298 i).centre ≤ (0.1 : ℝ) ∧ (cell12298 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12298 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12298 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12298

/-! The local source numeric instances at 12298 have no network premises. -/
namespace BstLean.Part264b.N12298
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12298 cell12298)

noncomputable def sourceNumerics12298 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12298 (cell12298 i)
      scalarRow12298.M scalarRow12298.H scalarRow12298.xi := by
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
    energy_allowance := scalarRow12298.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12298]
    centre_nonneg := (scalarRow12298.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12298]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12298
/-! Actual 12299 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12299
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12299 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12299 12299 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12299.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12299 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12299 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12299 := gPlus_lower 12299
end BstLean.Part264b.N12299

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12299
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036393481299 : ℝ) ≤ wn 12299 := by
  have hn : √(12299 : ℝ) ≤ 110.900856624285 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12299 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.900856624285 ≤ 2 / √12299 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260239971 : ℝ) ≤ rhoBar 12299 BstLean.Part154.csC ∧
    rhoBar 12299 BstLean.Part154.csC ≤ 0.000260268377 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036393481299 : ℝ) / (1.295212 * 12299) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12299) := by gcongr
      _ ≤ (0.000260268377 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12299 BstLean.Part154.csC) ≤ 0.001041141248 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12299 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12299 BstLean.Part154.csC) (piBar (rhoBar 12299 BstLean.Part154.csC)) ≤ 0.000198795050 ∧
    cc1 (rhoBar 12299 BstLean.Part154.csC) (piBar (rhoBar 12299 BstLean.Part154.csC)) ≤ 0.000126494547 ∧
    cc2 (rhoBar 12299 BstLean.Part154.csC) ≤ 0.000073430977 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12299 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12299 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12299 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12299 BstLean.Part154.csC * nuR (rhoBar 12299 BstLean.Part154.csC)) ≤ 0.000520553689 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260268377 : ℝ) * 0.001041141248 := by gcongr
      _ ≤ (0.000520553689 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12299 BstLean.Part154.csC) * nuR (rhoBar 12299 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001041141248 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12299 BstLean.Part154.csC) * rhoBar 12299 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260268377 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260268377 / 2 + 0.399 * 0.001041141248 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198795050 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000520553689 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126494547 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260268377 / 1.414213562 := by gcongr
      _ ≤ (0.000073430977 : ℝ) := by norm_num

end BstLean.Part264b.N12299

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12299
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12299 BstLean.Part154.csC) (piBar (rhoBar 12299 BstLean.Part154.csC)) ≤ 1.70666E-7 := by
  have hr0 : 0 ≤ rhoBar 12299 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12299 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12299 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12299 BstLean.Part154.csC) (piBar (rhoBar 12299 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12299 BstLean.Part154.csC) (piBar (rhoBar 12299 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12299 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198795050 : ℝ) ^ 2 + 0.000126494547 ^ 2 + 3 * 0.000073430977 ^ 2 +
        2 * 0.797885 * 0.000198795050 * 0.000126494547 + 2 * 0.000198795050 * 0.000073430977 +
        4 * 0.797885 * 0.000126494547 * 0.000073430977 := by gcongr
    _ ≤ (1.70666E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12299 BstLean.Part154.csC Θ ≤ 0.002718969906 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12299 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12299 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12299 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12299 BstLean.Part154.csC) (piBar (rhoBar 12299 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12299 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70666E-7 / (0.000260239971 : ℝ) := by gcongr
    _ ≤ 0.002718969906 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12299 BstLean.Part154.csC Θ ≤ 0.003018536749 + 0.000686962468 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12299 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12299 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12299 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260268377 +
        (6863 / 10000) * 0.000260268377 * 12299 * 0.001041141248) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003018536749 + 0.000686962468 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12299 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12299 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12299 0.011 Θ ∧ gammaRatio 12299 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12299 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12299) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12299 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12299 0.011 Θ) :=
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
    badAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12299 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12299 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12299 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12299 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12299 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12299 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12299 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12299 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12299 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12299 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12299 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004118536749 + 0.003405932374 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12299

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12299
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12299 BstLean.Part154.csC) (piBar (rhoBar 12299 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12299 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12299 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12299 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12299 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12299 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12299 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12299 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12299 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12299 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12299 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12299 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12299 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053342408801 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12299) ≤ 0.010768515388 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12299 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010768515388 + 2 * 0.737676 / 12299) := by gcongr
    _ ≤ (0.053342408801 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12299 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12299

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12299
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484842621 : ℝ) ≤ plow 12299 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12299) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053413251246)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427459201) : eMP 12299 0.011 xi bn ≤ 0.001228172994 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12299 : ℝ) * (1 - 0.011))) ≤ 0.000607188820 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001427459201 / (12299 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607188820 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607188820 : ℝ) + 3.141593 * 0.053413251246 / (12299 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001228172994 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053413251246)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427459201) : PiBarMP 12299 12 0.011 xi bn ≤ 0.163893128809 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12299 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037781731049 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.289215247910 : ℝ) ≤ √((12299 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.900856624284 : ℝ) ≤ √12299 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12299) ≤ 0.125629401674 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037781731049 + 0.053413251246 * 1.772454 / (2 * (110.289215247910 : ℝ))) * (1 + 0.001228172994) +
        8 / (12299 * 110.900856624284) + 0.125629401674 := by gcongr
    _ ≤ (0.163893128809 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053413251246)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427459201) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284455479064) :
    parallelOracle 12299 0.011 xi bn cd ≤ 0.164919020141 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12299 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12299 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484842621 : ℝ) ≤ plow 12299 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.900856624284 : ℝ) ≤ √12299 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284455479064 : ℝ) / (2 * 0.560484842621 * 110.900856624284)) * 0.163893128809 +
        0.284455479064 ^ 2 / (2 * 0.560484842621 * 110.900856624284) := by gcongr
    _ ≤ (0.164919020141 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053413251246) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001427459201)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284455479064) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12299 12299 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484842621 : ℝ) ≤ plow 12299 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.900856624284 : ℝ) ≤ √12299 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12299 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12299 Θ 1.22 ≤ 0.011957531623 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.900856624284 := by gcongr <;> linarith
      _ ≤ (0.011957531623 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12299 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12299 12299 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12299 12299 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12299 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12299 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12299 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12299 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164919020141 + 0.011957531623 + (0.008646 : ℝ) *
        (1 + 2 * (0.284455479064 + 0.011957531623) / (0.560484842621 * 110.900856624284))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12299]

end BstLean.Part264b.N12299

/-! The original eight local profiles supply actual 12299 moment certificates. -/
namespace BstLean.Part264b.N12299
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12299 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053413251246 ∧
    0 ≤ bN 12299 BstLean.Part154.csC (groupTheta g) ∧ bN 12299 BstLean.Part154.csC (groupTheta g) ≤ 0.001427459201 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12299 12299 0.011
      (momentAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12299 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12299 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12299 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231113070263 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12299 0.011
      (momentAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12299 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12299
/-! The actual computed-centre upper energy formula at 12299. -/
namespace BstLean.Part264b.N12299
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12299

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12299
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12299 cell12299)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086760344817
  | 2 => 0.087728870713
  | 3 => 0.088699675269
  | 4 => 0.089675098839
  | 5 => 0.090657936324
  | 6 => 0.091651499841
  | 7 => 0.092659686447
  | 8 => 0.093687050786
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12299 12299 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12299 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12299

/-! Actual upper energy certificates on all 43 source endpoints at 12299. -/
namespace BstLean.Part264b.N12299
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12299 cell12299)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12299 (gMinus 12299) (1 - (cell12299 i).lower) ≤ 1 ∧
    energyUpper 12299 (gMinus 12299) (BstLean.Part211.gPlus 12299)
      (finiteEnergy 12299 12299 0.011) (1 - (cell12299 i).lower) ≤
      (cell12299 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12299) (by norm_num)
        (q := 1 - (cell12299 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12299,cell12299]) (by norm_num [scalarRow12299,cell12299])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12299,cell12299])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12299

/-! Source-cell containment and simple scalar guards at 12299. -/
namespace BstLean.Part264b.N12299
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12299 cell12299)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12299 ⟨10,by decide⟩).lower ∧ (cell12299 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12299 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12299 ⟨11,by decide⟩).lower ∧ (cell12299 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12299 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12299 ⟨12,by decide⟩).lower ∧ (cell12299 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12299 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12299 ⟨13,by decide⟩).lower ∧ (cell12299 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12299 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12299 ⟨14,by decide⟩).lower ∧ (cell12299 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12299 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12299 ⟨15,by decide⟩).lower ∧ (cell12299 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12299 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12299 ⟨16,by decide⟩).lower ∧ (cell12299 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12299 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12299 ⟨17,by decide⟩).lower ∧ (cell12299 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12299 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12299 ⟨18,by decide⟩).lower ∧ (cell12299 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12299 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12299 ⟨19,by decide⟩).lower ∧ (cell12299 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12299 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12299 ⟨20,by decide⟩).lower ∧ (cell12299 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12299 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12299 ⟨21,by decide⟩).lower ∧ (cell12299 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12299 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12299 ⟨22,by decide⟩).lower ∧ (cell12299 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12299 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12299 ⟨23,by decide⟩).lower ∧ (cell12299 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12299 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12299 ⟨24,by decide⟩).lower ∧ (cell12299 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12299 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12299 ⟨25,by decide⟩).lower ∧ (cell12299 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12299 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12299 ⟨26,by decide⟩).lower ∧ (cell12299 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12299 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12299 ⟨27,by decide⟩).lower ∧ (cell12299 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12299 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12299 ⟨28,by decide⟩).lower ∧ (cell12299 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12299 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12299 ⟨29,by decide⟩).lower ∧ (cell12299 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12299 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12299 ⟨30,by decide⟩).lower ∧ (cell12299 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12299 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12299 ⟨31,by decide⟩).lower ∧ (cell12299 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12299 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12299 ⟨32,by decide⟩).lower ∧ (cell12299 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12299 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12299 ⟨33,by decide⟩).lower ∧ (cell12299 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12299 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12299 ⟨34,by decide⟩).lower ∧ (cell12299 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12299 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12299 ⟨35,by decide⟩).lower ∧ (cell12299 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12299 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12299 ⟨36,by decide⟩).lower ∧ (cell12299 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12299 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12299 ⟨37,by decide⟩).lower ∧ (cell12299 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12299 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12299 ⟨38,by decide⟩).lower ∧ (cell12299 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12299 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12299 ⟨39,by decide⟩).lower ∧ (cell12299 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12299 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12299 ⟨40,by decide⟩).lower ∧ (cell12299 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12299 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12299 ⟨41,by decide⟩).lower ∧ (cell12299 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12299 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12299 ⟨42,by decide⟩).lower ∧ (cell12299 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12299 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12299 ⟨43,by decide⟩).lower ∧ (cell12299 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12299 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12299 ⟨44,by decide⟩).lower ∧ (cell12299 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12299 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12299 ⟨45,by decide⟩).lower ∧ (cell12299 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12299 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12299 ⟨46,by decide⟩).lower ∧ (cell12299 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12299 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12299 ⟨47,by decide⟩).lower ∧ (cell12299 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12299 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12299 ⟨48,by decide⟩).lower ∧ (cell12299 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12299 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12299 ⟨49,by decide⟩).lower ∧ (cell12299 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12299 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12299 ⟨50,by decide⟩).lower ∧ (cell12299 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12299 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12299 ⟨51,by decide⟩).lower ∧ (cell12299 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12299 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12299 ⟨52,by decide⟩).lower ∧ (cell12299 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12299 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12299 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12299 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12299,cell12299,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12299 i).lower ∧
    (cell12299 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12299 i).upper ≤ (0.532 : ℝ) ∧
    (cell12299 i).centre ≤ (0.1 : ℝ) ∧ (cell12299 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12299 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12299 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12299

/-! The local source numeric instances at 12299 have no network premises. -/
namespace BstLean.Part264b.N12299
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12299 cell12299)

noncomputable def sourceNumerics12299 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12299 (cell12299 i)
      scalarRow12299.M scalarRow12299.H scalarRow12299.xi := by
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
    energy_allowance := scalarRow12299.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12299]
    centre_nonneg := (scalarRow12299.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12299]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12299
