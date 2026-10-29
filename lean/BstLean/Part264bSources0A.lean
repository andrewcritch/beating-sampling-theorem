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
namespace BstLean.Part264b.N12228
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12228 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12228 12228 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12228.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12228 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12228 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12228 := gPlus_lower 12228
end BstLean.Part264b.N12228

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12228
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036499930511 : ℝ) ≤ wn 12228 := by
  have hn : √(12228 : ℝ) ≤ 110.580287574233 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12228 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.580287574233 ≤ 2 / √12228 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261777899 : ℝ) ≤ rhoBar 12228 BstLean.Part154.csC ∧
    rhoBar 12228 BstLean.Part154.csC ≤ 0.000261779585 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036499930511 : ℝ) / (1.295212 * 12228) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12228) := by gcongr
      _ ≤ (0.000261779585 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12228 BstLean.Part154.csC) ≤ 0.001047186869 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12228 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12228 BstLean.Part154.csC) (piBar (rhoBar 12228 BstLean.Part154.csC)) ≤ 0.000199949379 ∧
    cc1 (rhoBar 12228 BstLean.Part154.csC) (piBar (rhoBar 12228 BstLean.Part154.csC)) ≤ 0.000127229042 ∧
    cc2 (rhoBar 12228 BstLean.Part154.csC) ≤ 0.000073857342 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12228 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12228 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12228 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12228 BstLean.Part154.csC * nuR (rhoBar 12228 BstLean.Part154.csC)) ≤ 0.000523576302 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261779585 : ℝ) * 0.001047186869 := by gcongr
      _ ≤ (0.000523576302 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12228 BstLean.Part154.csC) * nuR (rhoBar 12228 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001047186869 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12228 BstLean.Part154.csC) * rhoBar 12228 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261779585 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261779585 / 2 + 0.399 * 0.001047186869 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199949379 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523576302 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127229042 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261779585 / 1.414213562 := by gcongr
      _ ≤ (0.000073857342 : ℝ) := by norm_num

end BstLean.Part264b.N12228

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12228
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12228 BstLean.Part154.csC) (piBar (rhoBar 12228 BstLean.Part154.csC)) ≤ 1.72653E-7 := by
  have hr0 : 0 ≤ rhoBar 12228 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12228 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12228 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12228 BstLean.Part154.csC) (piBar (rhoBar 12228 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12228 BstLean.Part154.csC) (piBar (rhoBar 12228 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12228 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199949379 : ℝ) ^ 2 + 0.000127229042 ^ 2 + 3 * 0.000073857342 ^ 2 +
        2 * 0.797885 * 0.000199949379 * 0.000127229042 + 2 * 0.000199949379 * 0.000073857342 +
        4 * 0.797885 * 0.000127229042 * 0.000073857342 := by gcongr
    _ ≤ (1.72653E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12228 BstLean.Part154.csC Θ ≤ 0.002734466102 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12228 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12228 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12228 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12228 BstLean.Part154.csC) (piBar (rhoBar 12228 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12228 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72653E-7 / (0.000261777899 : ℝ) := by gcongr
    _ ≤ 0.002734466102 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12228 BstLean.Part154.csC Θ ≤ 0.003036064559 + 0.000690951209 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12228 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12228 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12228 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261779585 +
        (6863 / 10000) * 0.000261779585 * 12228 * 0.001047186869) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003036064559 + 0.000690951209 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12228 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12228 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12228 0.011 Θ ∧ gammaRatio 12228 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12228 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12228) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12228 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12228 0.011 Θ) :=
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
    badAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12228 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12228 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12228 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12228 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12228 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12228 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12228 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12228 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12228 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12228 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12228 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004136064559 + 0.003425417311 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12228

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12228
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12228 BstLean.Part154.csC) (piBar (rhoBar 12228 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12228 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12228 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12228 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12228 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12228 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12228 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12228 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12228 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12228 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12228 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12228 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12228 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053498755468 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12228) ≤ 0.010799733002 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12228 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010799733002 + 2 * 0.737676 / 12228) := by gcongr
    _ ≤ (0.053498755468 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12228 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12228

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12228
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481399124 : ℝ) ≤ plow 12228 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12228) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053441008648)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435594704) : eMP 12228 0.011 xi bn ≤ 0.001235246396 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12228 : ℝ) * (1 - 0.011))) ≤ 0.000610681865 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001435594704 / (12228 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610681865 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610681865 : ℝ) + 3.141593 * 0.053441008648 / (12228 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001235246396 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053441008648)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435594704) : PiBarMP 12228 12 0.011 xi bn ≤ 0.164366760334 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12228 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037889242590 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.970414203093 : ℝ) ≤ √((12228 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.580287574232 : ℝ) ≤ √12228 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12228) ≤ 0.125993597670 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037889242590 + 0.053441008648 * 1.772454 / (2 * (109.970414203093 : ℝ))) * (1 + 0.001235246396) +
        8 / (12228 * 110.580287574232) + 0.125993597670 := by gcongr
    _ ≤ (0.164366760334 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053441008648)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435594704) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284671869493) :
    parallelOracle 12228 0.011 xi bn cd ≤ 0.165397999367 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12228 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12228 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481399124 : ℝ) ≤ plow 12228 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.580287574232 : ℝ) ≤ √12228 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284671869493 : ℝ) / (2 * 0.560481399124 * 110.580287574232)) * 0.164366760334 +
        0.284671869493 ^ 2 / (2 * 0.560481399124 * 110.580287574232) := by gcongr
    _ ≤ (0.165397999367 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053441008648) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435594704)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284671869493) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12228 12228 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481399124 : ℝ) ≤ plow 12228 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.580287574232 : ℝ) ≤ √12228 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12228 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12228 Θ 1.22 ≤ 0.011992196160 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.580287574232 := by gcongr <;> linarith
      _ ≤ (0.011992196160 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12228 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12228 12228 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12228 12228 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12228 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12228 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12228 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12228 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165397999367 + 0.011992196160 + (0.008646 : ℝ) *
        (1 + 2 * (0.284671869493 + 0.011992196160) / (0.560481399124 * 110.580287574232))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12228]

end BstLean.Part264b.N12228

/-! The original eight local profiles supply actual 12228 moment certificates. -/
namespace BstLean.Part264b.N12228
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12228 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053441008648 ∧
    0 ≤ bN 12228 BstLean.Part154.csC (groupTheta g) ∧ bN 12228 BstLean.Part154.csC (groupTheta g) ≤ 0.001435594704 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12228 12228 0.011
      (momentAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12228 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12228 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12228 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231173114025 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12228 0.011
      (momentAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12228 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12228
/-! The actual computed-centre upper energy formula at 12228. -/
namespace BstLean.Part264b.N12228
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12228

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12228
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12228 cell12228)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.087010073761
  | 2 => 0.087984264334
  | 3 => 0.088961722539
  | 4 => 0.089945001950
  | 5 => 0.090937145779
  | 6 => 0.091941753437
  | 7 => 0.092963052279
  | 8 => 0.094005974396
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12228 12228 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12228 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12228

/-! Actual upper energy certificates on all 43 source endpoints at 12228. -/
namespace BstLean.Part264b.N12228
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12228 cell12228)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12228 (gMinus 12228) (1 - (cell12228 i).lower) ≤ 1 ∧
    energyUpper 12228 (gMinus 12228) (BstLean.Part211.gPlus 12228)
      (finiteEnergy 12228 12228 0.011) (1 - (cell12228 i).lower) ≤
      (cell12228 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12228) (by norm_num)
        (q := 1 - (cell12228 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12228,cell12228]) (by norm_num [scalarRow12228,cell12228])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12228,cell12228])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12228

/-! Source-cell containment and simple scalar guards at 12228. -/
namespace BstLean.Part264b.N12228
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12228 cell12228)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12228 ⟨10,by decide⟩).lower ∧ (cell12228 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12228 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12228 ⟨11,by decide⟩).lower ∧ (cell12228 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12228 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12228 ⟨12,by decide⟩).lower ∧ (cell12228 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12228 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12228 ⟨13,by decide⟩).lower ∧ (cell12228 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12228 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12228 ⟨14,by decide⟩).lower ∧ (cell12228 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12228 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12228 ⟨15,by decide⟩).lower ∧ (cell12228 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12228 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12228 ⟨16,by decide⟩).lower ∧ (cell12228 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12228 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12228 ⟨17,by decide⟩).lower ∧ (cell12228 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12228 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12228 ⟨18,by decide⟩).lower ∧ (cell12228 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12228 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12228 ⟨19,by decide⟩).lower ∧ (cell12228 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12228 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12228 ⟨20,by decide⟩).lower ∧ (cell12228 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12228 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12228 ⟨21,by decide⟩).lower ∧ (cell12228 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12228 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12228 ⟨22,by decide⟩).lower ∧ (cell12228 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12228 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12228 ⟨23,by decide⟩).lower ∧ (cell12228 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12228 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12228 ⟨24,by decide⟩).lower ∧ (cell12228 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12228 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12228 ⟨25,by decide⟩).lower ∧ (cell12228 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12228 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12228 ⟨26,by decide⟩).lower ∧ (cell12228 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12228 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12228 ⟨27,by decide⟩).lower ∧ (cell12228 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12228 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12228 ⟨28,by decide⟩).lower ∧ (cell12228 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12228 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12228 ⟨29,by decide⟩).lower ∧ (cell12228 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12228 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12228 ⟨30,by decide⟩).lower ∧ (cell12228 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12228 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12228 ⟨31,by decide⟩).lower ∧ (cell12228 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12228 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12228 ⟨32,by decide⟩).lower ∧ (cell12228 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12228 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12228 ⟨33,by decide⟩).lower ∧ (cell12228 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12228 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12228 ⟨34,by decide⟩).lower ∧ (cell12228 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12228 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12228 ⟨35,by decide⟩).lower ∧ (cell12228 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12228 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12228 ⟨36,by decide⟩).lower ∧ (cell12228 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12228 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12228 ⟨37,by decide⟩).lower ∧ (cell12228 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12228 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12228 ⟨38,by decide⟩).lower ∧ (cell12228 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12228 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12228 ⟨39,by decide⟩).lower ∧ (cell12228 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12228 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12228 ⟨40,by decide⟩).lower ∧ (cell12228 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12228 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12228 ⟨41,by decide⟩).lower ∧ (cell12228 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12228 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12228 ⟨42,by decide⟩).lower ∧ (cell12228 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12228 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12228 ⟨43,by decide⟩).lower ∧ (cell12228 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12228 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12228 ⟨44,by decide⟩).lower ∧ (cell12228 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12228 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12228 ⟨45,by decide⟩).lower ∧ (cell12228 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12228 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12228 ⟨46,by decide⟩).lower ∧ (cell12228 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12228 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12228 ⟨47,by decide⟩).lower ∧ (cell12228 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12228 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12228 ⟨48,by decide⟩).lower ∧ (cell12228 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12228 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12228 ⟨49,by decide⟩).lower ∧ (cell12228 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12228 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12228 ⟨50,by decide⟩).lower ∧ (cell12228 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12228 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12228 ⟨51,by decide⟩).lower ∧ (cell12228 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12228 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12228 ⟨52,by decide⟩).lower ∧ (cell12228 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12228 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12228 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12228 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12228,cell12228,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12228 i).lower ∧
    (cell12228 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12228 i).upper ≤ (0.532 : ℝ) ∧
    (cell12228 i).centre ≤ (0.1 : ℝ) ∧ (cell12228 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12228 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12228 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12228

/-! The local source numeric instances at 12228 have no network premises. -/
namespace BstLean.Part264b.N12228
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12228 cell12228)

noncomputable def sourceNumerics12228 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12228 (cell12228 i)
      scalarRow12228.M scalarRow12228.H scalarRow12228.xi := by
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
    energy_allowance := scalarRow12228.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12228]
    centre_nonneg := (scalarRow12228.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12228]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12228
/-! Actual 12229 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12229
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12229 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12229 12229 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12229.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12229 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12229 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12229 := gPlus_lower 12229
end BstLean.Part264b.N12229

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12229
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036498424755 : ℝ) ≤ wn 12229 := by
  have hn : √(12229 : ℝ) ≤ 110.584809083346 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12229 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.584809083346 ≤ 2 / √12229 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261756113 : ℝ) ≤ rhoBar 12229 BstLean.Part154.csC ∧
    rhoBar 12229 BstLean.Part154.csC ≤ 0.000261758178 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036498424755 : ℝ) / (1.295212 * 12229) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12229) := by gcongr
      _ ≤ (0.000261758178 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12229 BstLean.Part154.csC) ≤ 0.001047101230 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12229 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12229 BstLean.Part154.csC) (piBar (rhoBar 12229 BstLean.Part154.csC)) ≤ 0.000199933027 ∧
    cc1 (rhoBar 12229 BstLean.Part154.csC) (piBar (rhoBar 12229 BstLean.Part154.csC)) ≤ 0.000127218638 ∧
    cc2 (rhoBar 12229 BstLean.Part154.csC) ≤ 0.000073851303 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12229 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12229 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12229 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12229 BstLean.Part154.csC * nuR (rhoBar 12229 BstLean.Part154.csC)) ≤ 0.000523533486 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261758178 : ℝ) * 0.001047101230 := by gcongr
      _ ≤ (0.000523533486 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12229 BstLean.Part154.csC) * nuR (rhoBar 12229 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001047101230 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12229 BstLean.Part154.csC) * rhoBar 12229 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261758178 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261758178 / 2 + 0.399 * 0.001047101230 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199933027 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523533486 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127218638 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261758178 / 1.414213562 := by gcongr
      _ ≤ (0.000073851303 : ℝ) := by norm_num

end BstLean.Part264b.N12229

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12229
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12229 BstLean.Part154.csC) (piBar (rhoBar 12229 BstLean.Part154.csC)) ≤ 1.72625E-7 := by
  have hr0 : 0 ≤ rhoBar 12229 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12229 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12229 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12229 BstLean.Part154.csC) (piBar (rhoBar 12229 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12229 BstLean.Part154.csC) (piBar (rhoBar 12229 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12229 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199933027 : ℝ) ^ 2 + 0.000127218638 ^ 2 + 3 * 0.000073851303 ^ 2 +
        2 * 0.797885 * 0.000199933027 * 0.000127218638 + 2 * 0.000199933027 * 0.000073851303 +
        4 * 0.797885 * 0.000127218638 * 0.000073851303 := by gcongr
    _ ≤ (1.72625E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12229 BstLean.Part154.csC Θ ≤ 0.002734250194 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12229 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12229 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12229 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12229 BstLean.Part154.csC) (piBar (rhoBar 12229 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12229 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72625E-7 / (0.000261756113 : ℝ) := by gcongr
    _ ≤ 0.002734250194 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12229 BstLean.Part154.csC Θ ≤ 0.003035816263 + 0.000690894707 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12229 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12229 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12229 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261758178 +
        (6863 / 10000) * 0.000261758178 * 12229 * 0.001047101230) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003035816263 + 0.000690894707 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12229 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12229 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12229 0.011 Θ ∧ gammaRatio 12229 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12229 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12229) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12229 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12229 0.011 Θ) :=
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
    badAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12229 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12229 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12229 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12229 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12229 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12229 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12229 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12229 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12229 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12229 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12229 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004135816263 + 0.003425144901 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12229

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12229
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12229 BstLean.Part154.csC) (piBar (rhoBar 12229 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12229 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12229 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12229 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12229 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12229 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12229 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12229 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12229 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12229 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12229 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12229 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12229 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053496543886 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12229) ≤ 0.010799291431 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12229 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010799291431 + 2 * 0.737676 / 12229) := by gcongr
    _ ≤ (0.053496543886 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12229 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12229

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12229
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481447902 : ℝ) ≤ plow 12229 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12229) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053440617337)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435481352) : eMP 12229 0.011 xi bn ≤ 0.001235147005 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12229 : ℝ) * (1 - 0.011))) ≤ 0.000610632788 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001435481352 / (12229 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610632788 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610632788 : ℝ) + 3.141593 * 0.053440617337 / (12229 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001235147005 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053440617337)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435481352) : PiBarMP 12229 12 0.011 xi bn ≤ 0.164360085768 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12229 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037887746727 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.974910775139 : ℝ) ≤ √((12229 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.584809083345 : ℝ) ≤ √12229 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12229) ≤ 0.125988446137 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037887746727 + 0.053440617337 * 1.772454 / (2 * (109.974910775139 : ℝ))) * (1 + 0.001235147005) +
        8 / (12229 * 110.584809083345) + 0.125988446137 := by gcongr
    _ ≤ (0.164360085768 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053440617337)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435481352) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284668811551) :
    parallelOracle 12229 0.011 xi bn cd ≤ 0.165391249119 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12229 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12229 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481447902 : ℝ) ≤ plow 12229 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.584809083345 : ℝ) ≤ √12229 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284668811551 : ℝ) / (2 * 0.560481447902 * 110.584809083345)) * 0.164360085768 +
        0.284668811551 ^ 2 / (2 * 0.560481447902 * 110.584809083345) := by gcongr
    _ ≤ (0.165391249119 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053440617337) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435481352)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284668811551) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12229 12229 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481447902 : ℝ) ≤ plow 12229 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.584809083345 : ℝ) ≤ √12229 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12229 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12229 Θ 1.22 ≤ 0.011991705832 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.584809083345 := by gcongr <;> linarith
      _ ≤ (0.011991705832 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12229 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12229 12229 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12229 12229 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12229 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12229 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12229 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12229 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165391249119 + 0.011991705832 + (0.008646 : ℝ) *
        (1 + 2 * (0.284668811551 + 0.011991705832) / (0.560481447902 * 110.584809083345))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12229]

end BstLean.Part264b.N12229

/-! The original eight local profiles supply actual 12229 moment certificates. -/
namespace BstLean.Part264b.N12229
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12229 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053440617337 ∧
    0 ≤ bN 12229 BstLean.Part154.csC (groupTheta g) ∧ bN 12229 BstLean.Part154.csC (groupTheta g) ≤ 0.001435481352 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12229 12229 0.011
      (momentAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12229 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12229 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12229 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231172267665 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12229 0.011
      (momentAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12229 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12229
/-! The actual computed-centre upper energy formula at 12229. -/
namespace BstLean.Part264b.N12229
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12229

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12229
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12229 cell12229)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.087006495148
  | 2 => 0.087980603135
  | 3 => 0.088957964176
  | 4 => 0.089941128720
  | 5 => 0.090933136341
  | 6 => 0.091937582242
  | 7 => 0.092958688948
  | 8 => 0.094001383033
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12229 12229 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12229 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12229

/-! Actual upper energy certificates on all 43 source endpoints at 12229. -/
namespace BstLean.Part264b.N12229
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12229 cell12229)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12229 (gMinus 12229) (1 - (cell12229 i).lower) ≤ 1 ∧
    energyUpper 12229 (gMinus 12229) (BstLean.Part211.gPlus 12229)
      (finiteEnergy 12229 12229 0.011) (1 - (cell12229 i).lower) ≤
      (cell12229 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12229) (by norm_num)
        (q := 1 - (cell12229 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12229,cell12229]) (by norm_num [scalarRow12229,cell12229])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12229,cell12229])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12229

/-! Source-cell containment and simple scalar guards at 12229. -/
namespace BstLean.Part264b.N12229
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12229 cell12229)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12229 ⟨10,by decide⟩).lower ∧ (cell12229 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12229 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12229 ⟨11,by decide⟩).lower ∧ (cell12229 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12229 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12229 ⟨12,by decide⟩).lower ∧ (cell12229 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12229 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12229 ⟨13,by decide⟩).lower ∧ (cell12229 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12229 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12229 ⟨14,by decide⟩).lower ∧ (cell12229 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12229 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12229 ⟨15,by decide⟩).lower ∧ (cell12229 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12229 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12229 ⟨16,by decide⟩).lower ∧ (cell12229 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12229 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12229 ⟨17,by decide⟩).lower ∧ (cell12229 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12229 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12229 ⟨18,by decide⟩).lower ∧ (cell12229 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12229 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12229 ⟨19,by decide⟩).lower ∧ (cell12229 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12229 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12229 ⟨20,by decide⟩).lower ∧ (cell12229 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12229 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12229 ⟨21,by decide⟩).lower ∧ (cell12229 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12229 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12229 ⟨22,by decide⟩).lower ∧ (cell12229 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12229 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12229 ⟨23,by decide⟩).lower ∧ (cell12229 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12229 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12229 ⟨24,by decide⟩).lower ∧ (cell12229 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12229 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12229 ⟨25,by decide⟩).lower ∧ (cell12229 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12229 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12229 ⟨26,by decide⟩).lower ∧ (cell12229 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12229 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12229 ⟨27,by decide⟩).lower ∧ (cell12229 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12229 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12229 ⟨28,by decide⟩).lower ∧ (cell12229 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12229 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12229 ⟨29,by decide⟩).lower ∧ (cell12229 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12229 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12229 ⟨30,by decide⟩).lower ∧ (cell12229 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12229 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12229 ⟨31,by decide⟩).lower ∧ (cell12229 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12229 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12229 ⟨32,by decide⟩).lower ∧ (cell12229 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12229 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12229 ⟨33,by decide⟩).lower ∧ (cell12229 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12229 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12229 ⟨34,by decide⟩).lower ∧ (cell12229 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12229 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12229 ⟨35,by decide⟩).lower ∧ (cell12229 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12229 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12229 ⟨36,by decide⟩).lower ∧ (cell12229 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12229 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12229 ⟨37,by decide⟩).lower ∧ (cell12229 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12229 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12229 ⟨38,by decide⟩).lower ∧ (cell12229 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12229 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12229 ⟨39,by decide⟩).lower ∧ (cell12229 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12229 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12229 ⟨40,by decide⟩).lower ∧ (cell12229 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12229 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12229 ⟨41,by decide⟩).lower ∧ (cell12229 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12229 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12229 ⟨42,by decide⟩).lower ∧ (cell12229 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12229 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12229 ⟨43,by decide⟩).lower ∧ (cell12229 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12229 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12229 ⟨44,by decide⟩).lower ∧ (cell12229 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12229 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12229 ⟨45,by decide⟩).lower ∧ (cell12229 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12229 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12229 ⟨46,by decide⟩).lower ∧ (cell12229 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12229 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12229 ⟨47,by decide⟩).lower ∧ (cell12229 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12229 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12229 ⟨48,by decide⟩).lower ∧ (cell12229 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12229 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12229 ⟨49,by decide⟩).lower ∧ (cell12229 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12229 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12229 ⟨50,by decide⟩).lower ∧ (cell12229 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12229 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12229 ⟨51,by decide⟩).lower ∧ (cell12229 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12229 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12229 ⟨52,by decide⟩).lower ∧ (cell12229 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12229 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12229 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12229 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12229,cell12229,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12229 i).lower ∧
    (cell12229 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12229 i).upper ≤ (0.532 : ℝ) ∧
    (cell12229 i).centre ≤ (0.1 : ℝ) ∧ (cell12229 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12229 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12229 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12229

/-! The local source numeric instances at 12229 have no network premises. -/
namespace BstLean.Part264b.N12229
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12229 cell12229)

noncomputable def sourceNumerics12229 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12229 (cell12229 i)
      scalarRow12229.M scalarRow12229.H scalarRow12229.xi := by
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
    energy_allowance := scalarRow12229.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12229]
    centre_nonneg := (scalarRow12229.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12229]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12229
/-! Actual 12230 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12230
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12230 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12230 12230 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12230.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12230 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12230 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12230 := gPlus_lower 12230
end BstLean.Part264b.N12230

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12230
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036496919184 : ℝ) ≤ wn 12230 := by
  have hn : √(12230 : ℝ) ≤ 110.589330407595 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12230 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.589330407595 ≤ 2 / √12230 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261734330 : ℝ) ≤ rhoBar 12230 BstLean.Part154.csC ∧
    rhoBar 12230 BstLean.Part154.csC ≤ 0.000261736775 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036496919184 : ℝ) / (1.295212 * 12230) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12230) := by gcongr
      _ ≤ (0.000261736775 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12230 BstLean.Part154.csC) ≤ 0.001047015607 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12230 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12230 BstLean.Part154.csC) (piBar (rhoBar 12230 BstLean.Part154.csC)) ≤ 0.000199916678 ∧
    cc1 (rhoBar 12230 BstLean.Part154.csC) (piBar (rhoBar 12230 BstLean.Part154.csC)) ≤ 0.000127208235 ∧
    cc2 (rhoBar 12230 BstLean.Part154.csC) ≤ 0.000073845264 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12230 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12230 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12230 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12230 BstLean.Part154.csC * nuR (rhoBar 12230 BstLean.Part154.csC)) ≤ 0.000523490677 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261736775 : ℝ) * 0.001047015607 := by gcongr
      _ ≤ (0.000523490677 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12230 BstLean.Part154.csC) * nuR (rhoBar 12230 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001047015607 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12230 BstLean.Part154.csC) * rhoBar 12230 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261736775 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261736775 / 2 + 0.399 * 0.001047015607 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199916678 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523490677 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127208235 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261736775 / 1.414213562 := by gcongr
      _ ≤ (0.000073845264 : ℝ) := by norm_num

end BstLean.Part264b.N12230

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12230
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12230 BstLean.Part154.csC) (piBar (rhoBar 12230 BstLean.Part154.csC)) ≤ 1.72597E-7 := by
  have hr0 : 0 ≤ rhoBar 12230 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12230 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12230 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12230 BstLean.Part154.csC) (piBar (rhoBar 12230 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12230 BstLean.Part154.csC) (piBar (rhoBar 12230 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12230 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199916678 : ℝ) ^ 2 + 0.000127208235 ^ 2 + 3 * 0.000073845264 ^ 2 +
        2 * 0.797885 * 0.000199916678 * 0.000127208235 + 2 * 0.000199916678 * 0.000073845264 +
        4 * 0.797885 * 0.000127208235 * 0.000073845264 := by gcongr
    _ ≤ (1.72597E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12230 BstLean.Part154.csC Θ ≤ 0.002734034217 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12230 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12230 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12230 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12230 BstLean.Part154.csC) (piBar (rhoBar 12230 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12230 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72597E-7 / (0.000261734330 : ℝ) := by gcongr
    _ ≤ 0.002734034217 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12230 BstLean.Part154.csC Θ ≤ 0.003035568019 + 0.000690838215 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12230 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12230 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12230 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261736775 +
        (6863 / 10000) * 0.000261736775 * 12230 * 0.001047015607) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003035568019 + 0.000690838215 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12230 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12230 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12230 0.011 Θ ∧ gammaRatio 12230 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12230 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12230) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12230 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12230 0.011 Θ) :=
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
    badAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12230 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12230 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12230 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12230 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12230 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12230 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12230 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12230 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12230 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12230 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12230 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004135568019 + 0.003424872432 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12230

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12230
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12230 BstLean.Part154.csC) (piBar (rhoBar 12230 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12230 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12230 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12230 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12230 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12230 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12230 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12230 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12230 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12230 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12230 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12230 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12230 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053494332576 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12230) ≤ 0.010798849914 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12230 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010798849914 + 2 * 0.737676 / 12230) := by gcongr
    _ ≤ (0.053494332576 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12230 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12230

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12230
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481496672 : ℝ) ≤ plow 12230 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12230) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053440226046)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435367964) : eMP 12230 0.011 xi bn ≤ 0.001235047604 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12230 : ℝ) * (1 - 0.011))) ≤ 0.000610583706 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001435367964 / (12230 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610583706 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610583706 : ℝ) + 3.141593 * 0.053440226046 / (12230 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001235047604 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053440226046)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435367964) : PiBarMP 12230 12 0.011 xi bn ≤ 0.164353411303 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12230 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037886250330 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.979407163341 : ℝ) ≤ √((12230 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.589330407594 : ℝ) ≤ √12230 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12230) ≤ 0.125983295237 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037886250330 + 0.053440226046 * 1.772454 / (2 * (109.979407163341 : ℝ))) * (1 + 0.001235047604) +
        8 / (12230 * 110.589330407594) + 0.125983295237 := by gcongr
    _ ≤ (0.164353411303 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053440226046)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435367964) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284665753920) :
    parallelOracle 12230 0.011 xi bn cd ≤ 0.165384498984 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12230 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12230 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481496672 : ℝ) ≤ plow 12230 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.589330407594 : ℝ) ≤ √12230 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284665753920 : ℝ) / (2 * 0.560481496672 * 110.589330407594)) * 0.164353411303 +
        0.284665753920 ^ 2 / (2 * 0.560481496672 * 110.589330407594) := by gcongr
    _ ≤ (0.165384498984 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053440226046) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435367964)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284665753920) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12230 12230 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481496672 : ℝ) ≤ plow 12230 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.589330407594 : ℝ) ≤ √12230 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12230 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12230 Θ 1.22 ≤ 0.011991215565 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.589330407594 := by gcongr <;> linarith
      _ ≤ (0.011991215565 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12230 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12230 12230 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12230 12230 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12230 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12230 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12230 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12230 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165384498984 + 0.011991215565 + (0.008646 : ℝ) *
        (1 + 2 * (0.284665753920 + 0.011991215565) / (0.560481496672 * 110.589330407594))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12230]

end BstLean.Part264b.N12230

/-! The original eight local profiles supply actual 12230 moment certificates. -/
namespace BstLean.Part264b.N12230
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12230 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053440226046 ∧
    0 ≤ bN 12230 BstLean.Part154.csC (groupTheta g) ∧ bN 12230 BstLean.Part154.csC (groupTheta g) ≤ 0.001435367964 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12230 12230 0.011
      (momentAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12230 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12230 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12230 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231171421344 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12230 0.011
      (momentAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12230 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12230
/-! The actual computed-centre upper energy formula at 12230. -/
namespace BstLean.Part264b.N12230
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12230

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12230
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12230 cell12230)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.087002918332
  | 2 => 0.087976943815
  | 3 => 0.088954207794
  | 4 => 0.089937257596
  | 5 => 0.090929129159
  | 6 => 0.091933413486
  | 7 => 0.092954328276
  | 8 => 0.093996794589
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12230 12230 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12230 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12230

/-! Actual upper energy certificates on all 43 source endpoints at 12230. -/
namespace BstLean.Part264b.N12230
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12230 cell12230)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12230 (gMinus 12230) (1 - (cell12230 i).lower) ≤ 1 ∧
    energyUpper 12230 (gMinus 12230) (BstLean.Part211.gPlus 12230)
      (finiteEnergy 12230 12230 0.011) (1 - (cell12230 i).lower) ≤
      (cell12230 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12230) (by norm_num)
        (q := 1 - (cell12230 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12230,cell12230]) (by norm_num [scalarRow12230,cell12230])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12230,cell12230])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12230

/-! Source-cell containment and simple scalar guards at 12230. -/
namespace BstLean.Part264b.N12230
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12230 cell12230)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12230 ⟨10,by decide⟩).lower ∧ (cell12230 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12230 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12230 ⟨11,by decide⟩).lower ∧ (cell12230 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12230 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12230 ⟨12,by decide⟩).lower ∧ (cell12230 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12230 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12230 ⟨13,by decide⟩).lower ∧ (cell12230 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12230 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12230 ⟨14,by decide⟩).lower ∧ (cell12230 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12230 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12230 ⟨15,by decide⟩).lower ∧ (cell12230 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12230 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12230 ⟨16,by decide⟩).lower ∧ (cell12230 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12230 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12230 ⟨17,by decide⟩).lower ∧ (cell12230 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12230 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12230 ⟨18,by decide⟩).lower ∧ (cell12230 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12230 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12230 ⟨19,by decide⟩).lower ∧ (cell12230 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12230 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12230 ⟨20,by decide⟩).lower ∧ (cell12230 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12230 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12230 ⟨21,by decide⟩).lower ∧ (cell12230 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12230 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12230 ⟨22,by decide⟩).lower ∧ (cell12230 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12230 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12230 ⟨23,by decide⟩).lower ∧ (cell12230 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12230 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12230 ⟨24,by decide⟩).lower ∧ (cell12230 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12230 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12230 ⟨25,by decide⟩).lower ∧ (cell12230 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12230 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12230 ⟨26,by decide⟩).lower ∧ (cell12230 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12230 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12230 ⟨27,by decide⟩).lower ∧ (cell12230 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12230 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12230 ⟨28,by decide⟩).lower ∧ (cell12230 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12230 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12230 ⟨29,by decide⟩).lower ∧ (cell12230 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12230 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12230 ⟨30,by decide⟩).lower ∧ (cell12230 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12230 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12230 ⟨31,by decide⟩).lower ∧ (cell12230 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12230 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12230 ⟨32,by decide⟩).lower ∧ (cell12230 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12230 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12230 ⟨33,by decide⟩).lower ∧ (cell12230 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12230 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12230 ⟨34,by decide⟩).lower ∧ (cell12230 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12230 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12230 ⟨35,by decide⟩).lower ∧ (cell12230 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12230 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12230 ⟨36,by decide⟩).lower ∧ (cell12230 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12230 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12230 ⟨37,by decide⟩).lower ∧ (cell12230 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12230 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12230 ⟨38,by decide⟩).lower ∧ (cell12230 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12230 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12230 ⟨39,by decide⟩).lower ∧ (cell12230 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12230 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12230 ⟨40,by decide⟩).lower ∧ (cell12230 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12230 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12230 ⟨41,by decide⟩).lower ∧ (cell12230 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12230 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12230 ⟨42,by decide⟩).lower ∧ (cell12230 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12230 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12230 ⟨43,by decide⟩).lower ∧ (cell12230 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12230 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12230 ⟨44,by decide⟩).lower ∧ (cell12230 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12230 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12230 ⟨45,by decide⟩).lower ∧ (cell12230 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12230 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12230 ⟨46,by decide⟩).lower ∧ (cell12230 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12230 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12230 ⟨47,by decide⟩).lower ∧ (cell12230 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12230 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12230 ⟨48,by decide⟩).lower ∧ (cell12230 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12230 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12230 ⟨49,by decide⟩).lower ∧ (cell12230 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12230 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12230 ⟨50,by decide⟩).lower ∧ (cell12230 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12230 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12230 ⟨51,by decide⟩).lower ∧ (cell12230 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12230 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12230 ⟨52,by decide⟩).lower ∧ (cell12230 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12230 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12230 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12230 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12230,cell12230,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12230 i).lower ∧
    (cell12230 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12230 i).upper ≤ (0.532 : ℝ) ∧
    (cell12230 i).centre ≤ (0.1 : ℝ) ∧ (cell12230 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12230 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12230 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12230

/-! The local source numeric instances at 12230 have no network premises. -/
namespace BstLean.Part264b.N12230
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12230 cell12230)

noncomputable def sourceNumerics12230 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12230 (cell12230 i)
      scalarRow12230.M scalarRow12230.H scalarRow12230.xi := by
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
    energy_allowance := scalarRow12230.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12230]
    centre_nonneg := (scalarRow12230.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12230]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12230
/-! Actual 12231 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12231
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12231 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12231 12231 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12231.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12231 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12231 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12231 := gPlus_lower 12231
end BstLean.Part264b.N12231

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12231
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036495413800 : ℝ) ≤ wn 12231 := by
  have hn : √(12231 : ℝ) ≤ 110.593851547001 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12231 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.593851547001 ≤ 2 / √12231 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261712550 : ℝ) ≤ rhoBar 12231 BstLean.Part154.csC ∧
    rhoBar 12231 BstLean.Part154.csC ≤ 0.000261715376 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036495413800 : ℝ) / (1.295212 * 12231) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12231) := by gcongr
      _ ≤ (0.000261715376 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12231 BstLean.Part154.csC) ≤ 0.001046929999 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12231 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12231 BstLean.Part154.csC) (piBar (rhoBar 12231 BstLean.Part154.csC)) ≤ 0.000199900333 ∧
    cc1 (rhoBar 12231 BstLean.Part154.csC) (piBar (rhoBar 12231 BstLean.Part154.csC)) ≤ 0.000127197834 ∧
    cc2 (rhoBar 12231 BstLean.Part154.csC) ≤ 0.000073839227 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12231 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12231 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12231 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12231 BstLean.Part154.csC * nuR (rhoBar 12231 BstLean.Part154.csC)) ≤ 0.000523447876 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261715376 : ℝ) * 0.001046929999 := by gcongr
      _ ≤ (0.000523447876 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12231 BstLean.Part154.csC) * nuR (rhoBar 12231 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046929999 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12231 BstLean.Part154.csC) * rhoBar 12231 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261715376 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261715376 / 2 + 0.399 * 0.001046929999 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199900333 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523447876 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127197834 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261715376 / 1.414213562 := by gcongr
      _ ≤ (0.000073839227 : ℝ) := by norm_num

end BstLean.Part264b.N12231

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12231
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12231 BstLean.Part154.csC) (piBar (rhoBar 12231 BstLean.Part154.csC)) ≤ 1.72569E-7 := by
  have hr0 : 0 ≤ rhoBar 12231 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12231 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12231 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12231 BstLean.Part154.csC) (piBar (rhoBar 12231 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12231 BstLean.Part154.csC) (piBar (rhoBar 12231 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12231 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199900333 : ℝ) ^ 2 + 0.000127197834 ^ 2 + 3 * 0.000073839227 ^ 2 +
        2 * 0.797885 * 0.000199900333 * 0.000127197834 + 2 * 0.000199900333 * 0.000073839227 +
        4 * 0.797885 * 0.000127197834 * 0.000073839227 := by gcongr
    _ ≤ (1.72569E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12231 BstLean.Part154.csC Θ ≤ 0.002733818174 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12231 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12231 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12231 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12231 BstLean.Part154.csC) (piBar (rhoBar 12231 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12231 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72569E-7 / (0.000261712550 : ℝ) := by gcongr
    _ ≤ 0.002733818174 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12231 BstLean.Part154.csC Θ ≤ 0.003035319825 + 0.000690781734 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12231 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12231 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12231 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261715376 +
        (6863 / 10000) * 0.000261715376 * 12231 * 0.001046929999) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003035319825 + 0.000690781734 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12231 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12231 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12231 0.011 Θ ∧ gammaRatio 12231 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12231 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12231) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12231 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12231 0.011 Θ) :=
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
    badAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12231 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12231 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12231 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12231 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12231 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12231 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12231 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12231 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12231 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12231 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12231 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004135319825 + 0.003424599908 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12231

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12231
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12231 BstLean.Part154.csC) (piBar (rhoBar 12231 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12231 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12231 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12231 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12231 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12231 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12231 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12231 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12231 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12231 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12231 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12231 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12231 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053492121535 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12231) ≤ 0.010798408450 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12231 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010798408450 + 2 * 0.737676 / 12231) := by gcongr
    _ ≤ (0.053492121535 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12231 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12231

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12231
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481545433 : ℝ) ≤ plow 12231 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12231) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439834777)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435254542) : eMP 12231 0.011 xi bn ≤ 0.001234948200 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12231 : ℝ) * (1 - 0.011))) ≤ 0.000610534622 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001435254542 / (12231 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610534622 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610534622 : ℝ) + 3.141593 * 0.053439834777 / (12231 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001234948200 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439834777)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435254542) : PiBarMP 12231 12 0.011 xi bn ≤ 0.164346736963 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12231 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037884753425 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.983903367720 : ℝ) ≤ √((12231 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.593851547000 : ℝ) ≤ √12231 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12231) ≤ 0.125978144968 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037884753425 + 0.053439834777 * 1.772454 / (2 * (109.983903367720 : ℝ))) * (1 + 0.001234948200) +
        8 / (12231 * 110.593851547000) + 0.125978144968 := by gcongr
    _ ≤ (0.164346736963 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439834777)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435254542) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284662696603) :
    parallelOracle 12231 0.011 xi bn cd ≤ 0.165377748983 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12231 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12231 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481545433 : ℝ) ≤ plow 12231 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.593851547000 : ℝ) ≤ √12231 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284662696603 : ℝ) / (2 * 0.560481545433 * 110.593851547000)) * 0.164346736963 +
        0.284662696603 ^ 2 / (2 * 0.560481545433 * 110.593851547000) := by gcongr
    _ ≤ (0.165377748983 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439834777) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435254542)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284662696603) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12231 12231 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481545433 : ℝ) ≤ plow 12231 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.593851547000 : ℝ) ≤ √12231 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12231 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12231 Θ 1.22 ≤ 0.011990725357 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.593851547000 := by gcongr <;> linarith
      _ ≤ (0.011990725357 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12231 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12231 12231 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12231 12231 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12231 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12231 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12231 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12231 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165377748983 + 0.011990725357 + (0.008646 : ℝ) *
        (1 + 2 * (0.284662696603 + 0.011990725357) / (0.560481545433 * 110.593851547000))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12231]

end BstLean.Part264b.N12231

/-! The original eight local profiles supply actual 12231 moment certificates. -/
namespace BstLean.Part264b.N12231
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12231 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053439834777 ∧
    0 ≤ bN 12231 BstLean.Part154.csC (groupTheta g) ∧ bN 12231 BstLean.Part154.csC (groupTheta g) ≤ 0.001435254542 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12231 12231 0.011
      (momentAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12231 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12231 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12231 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231170575068 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12231 0.011
      (momentAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12231 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12231
/-! The actual computed-centre upper energy formula at 12231. -/
namespace BstLean.Part264b.N12231
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12231

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12231
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12231 cell12231)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086999343312
  | 2 => 0.087973286372
  | 3 => 0.088950453391
  | 4 => 0.089933388575
  | 5 => 0.090925124231
  | 6 => 0.091929247167
  | 7 => 0.092949970259
  | 8 => 0.093992209063
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12231 12231 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12231 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12231

/-! Actual upper energy certificates on all 43 source endpoints at 12231. -/
namespace BstLean.Part264b.N12231
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12231 cell12231)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12231 (gMinus 12231) (1 - (cell12231 i).lower) ≤ 1 ∧
    energyUpper 12231 (gMinus 12231) (BstLean.Part211.gPlus 12231)
      (finiteEnergy 12231 12231 0.011) (1 - (cell12231 i).lower) ≤
      (cell12231 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12231) (by norm_num)
        (q := 1 - (cell12231 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12231,cell12231]) (by norm_num [scalarRow12231,cell12231])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12231,cell12231])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12231

/-! Source-cell containment and simple scalar guards at 12231. -/
namespace BstLean.Part264b.N12231
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12231 cell12231)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12231 ⟨10,by decide⟩).lower ∧ (cell12231 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12231 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12231 ⟨11,by decide⟩).lower ∧ (cell12231 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12231 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12231 ⟨12,by decide⟩).lower ∧ (cell12231 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12231 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12231 ⟨13,by decide⟩).lower ∧ (cell12231 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12231 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12231 ⟨14,by decide⟩).lower ∧ (cell12231 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12231 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12231 ⟨15,by decide⟩).lower ∧ (cell12231 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12231 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12231 ⟨16,by decide⟩).lower ∧ (cell12231 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12231 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12231 ⟨17,by decide⟩).lower ∧ (cell12231 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12231 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12231 ⟨18,by decide⟩).lower ∧ (cell12231 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12231 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12231 ⟨19,by decide⟩).lower ∧ (cell12231 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12231 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12231 ⟨20,by decide⟩).lower ∧ (cell12231 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12231 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12231 ⟨21,by decide⟩).lower ∧ (cell12231 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12231 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12231 ⟨22,by decide⟩).lower ∧ (cell12231 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12231 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12231 ⟨23,by decide⟩).lower ∧ (cell12231 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12231 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12231 ⟨24,by decide⟩).lower ∧ (cell12231 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12231 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12231 ⟨25,by decide⟩).lower ∧ (cell12231 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12231 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12231 ⟨26,by decide⟩).lower ∧ (cell12231 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12231 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12231 ⟨27,by decide⟩).lower ∧ (cell12231 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12231 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12231 ⟨28,by decide⟩).lower ∧ (cell12231 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12231 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12231 ⟨29,by decide⟩).lower ∧ (cell12231 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12231 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12231 ⟨30,by decide⟩).lower ∧ (cell12231 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12231 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12231 ⟨31,by decide⟩).lower ∧ (cell12231 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12231 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12231 ⟨32,by decide⟩).lower ∧ (cell12231 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12231 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12231 ⟨33,by decide⟩).lower ∧ (cell12231 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12231 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12231 ⟨34,by decide⟩).lower ∧ (cell12231 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12231 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12231 ⟨35,by decide⟩).lower ∧ (cell12231 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12231 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12231 ⟨36,by decide⟩).lower ∧ (cell12231 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12231 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12231 ⟨37,by decide⟩).lower ∧ (cell12231 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12231 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12231 ⟨38,by decide⟩).lower ∧ (cell12231 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12231 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12231 ⟨39,by decide⟩).lower ∧ (cell12231 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12231 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12231 ⟨40,by decide⟩).lower ∧ (cell12231 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12231 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12231 ⟨41,by decide⟩).lower ∧ (cell12231 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12231 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12231 ⟨42,by decide⟩).lower ∧ (cell12231 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12231 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12231 ⟨43,by decide⟩).lower ∧ (cell12231 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12231 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12231 ⟨44,by decide⟩).lower ∧ (cell12231 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12231 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12231 ⟨45,by decide⟩).lower ∧ (cell12231 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12231 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12231 ⟨46,by decide⟩).lower ∧ (cell12231 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12231 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12231 ⟨47,by decide⟩).lower ∧ (cell12231 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12231 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12231 ⟨48,by decide⟩).lower ∧ (cell12231 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12231 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12231 ⟨49,by decide⟩).lower ∧ (cell12231 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12231 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12231 ⟨50,by decide⟩).lower ∧ (cell12231 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12231 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12231 ⟨51,by decide⟩).lower ∧ (cell12231 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12231 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12231 ⟨52,by decide⟩).lower ∧ (cell12231 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12231 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12231 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12231 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12231,cell12231,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12231 i).lower ∧
    (cell12231 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12231 i).upper ≤ (0.532 : ℝ) ∧
    (cell12231 i).centre ≤ (0.1 : ℝ) ∧ (cell12231 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12231 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12231 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12231

/-! The local source numeric instances at 12231 have no network premises. -/
namespace BstLean.Part264b.N12231
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12231 cell12231)

noncomputable def sourceNumerics12231 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12231 (cell12231 i)
      scalarRow12231.M scalarRow12231.H scalarRow12231.xi := by
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
    energy_allowance := scalarRow12231.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12231]
    centre_nonneg := (scalarRow12231.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12231]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12231
/-! Actual 12232 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12232
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12232 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12232 12232 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12232.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12232 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12232 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12232 := gPlus_lower 12232
end BstLean.Part264b.N12232

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12232
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036493908600 : ℝ) ≤ wn 12232 := by
  have hn : √(12232 : ℝ) ≤ 110.598372501588 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12232 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.598372501588 ≤ 2 / √12232 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261690775 : ℝ) ≤ rhoBar 12232 BstLean.Part154.csC ∧
    rhoBar 12232 BstLean.Part154.csC ≤ 0.000261693980 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036493908600 : ℝ) / (1.295212 * 12232) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12232) := by gcongr
      _ ≤ (0.000261693980 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12232 BstLean.Part154.csC) ≤ 0.001046844404 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12232 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12232 BstLean.Part154.csC) (piBar (rhoBar 12232 BstLean.Part154.csC)) ≤ 0.000199883990 ∧
    cc1 (rhoBar 12232 BstLean.Part154.csC) (piBar (rhoBar 12232 BstLean.Part154.csC)) ≤ 0.000127187435 ∧
    cc2 (rhoBar 12232 BstLean.Part154.csC) ≤ 0.000073833190 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12232 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12232 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12232 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12232 BstLean.Part154.csC * nuR (rhoBar 12232 BstLean.Part154.csC)) ≤ 0.000523405081 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261693980 : ℝ) * 0.001046844404 := by gcongr
      _ ≤ (0.000523405081 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12232 BstLean.Part154.csC) * nuR (rhoBar 12232 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046844404 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12232 BstLean.Part154.csC) * rhoBar 12232 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261693980 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261693980 / 2 + 0.399 * 0.001046844404 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199883990 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523405081 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127187435 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261693980 / 1.414213562 := by gcongr
      _ ≤ (0.000073833190 : ℝ) := by norm_num

end BstLean.Part264b.N12232

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12232
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12232 BstLean.Part154.csC) (piBar (rhoBar 12232 BstLean.Part154.csC)) ≤ 1.72540E-7 := by
  have hr0 : 0 ≤ rhoBar 12232 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12232 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12232 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12232 BstLean.Part154.csC) (piBar (rhoBar 12232 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12232 BstLean.Part154.csC) (piBar (rhoBar 12232 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12232 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199883990 : ℝ) ^ 2 + 0.000127187435 ^ 2 + 3 * 0.000073833190 ^ 2 +
        2 * 0.797885 * 0.000199883990 * 0.000127187435 + 2 * 0.000199883990 * 0.000073833190 +
        4 * 0.797885 * 0.000127187435 * 0.000073833190 := by gcongr
    _ ≤ (1.72540E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12232 BstLean.Part154.csC Θ ≤ 0.002733586199 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12232 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12232 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12232 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12232 BstLean.Part154.csC) (piBar (rhoBar 12232 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12232 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72540E-7 / (0.000261690775 : ℝ) := by gcongr
    _ ≤ 0.002733586199 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12232 BstLean.Part154.csC Θ ≤ 0.003035071663 + 0.000690725260 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12232 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12232 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12232 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261693980 +
        (6863 / 10000) * 0.000261693980 * 12232 * 0.001046844404) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003035071663 + 0.000690725260 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12232 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12232 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12232 0.011 Θ ∧ gammaRatio 12232 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12232 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12232) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12232 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12232 0.011 Θ) :=
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
    badAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12232 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12232 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12232 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12232 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12232 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12232 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12232 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12232 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12232 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12232 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12232 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004135071663 + 0.003424311459 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12232

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12232
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12232 BstLean.Part154.csC) (piBar (rhoBar 12232 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12232 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12232 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12232 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12232 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12232 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12232 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12232 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12232 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12232 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12232 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12232 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12232 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053489910770 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12232) ≤ 0.010797967041 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12232 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010797967041 + 2 * 0.737676 / 12232) := by gcongr
    _ ≤ (0.053489910770 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12232 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12232

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12232
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481594187 : ℝ) ≤ plow 12232 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12232) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439435179)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435132755) : eMP 12232 0.011 xi bn ≤ 0.001234845241 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12232 : ℝ) * (1 - 0.011))) ≤ 0.000610483762 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001435132755 / (12232 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610483762 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610483762 : ℝ) + 3.141593 * 0.053439435179 / (12232 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001234845241 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439435179)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435132755) : PiBarMP 12232 12 0.011 xi bn ≤ 0.164339952454 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12232 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037883146055 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.988399388299 : ℝ) ≤ √((12232 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.598372501587 : ℝ) ≤ √12232 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12232) ≤ 0.125972995331 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037883146055 + 0.053439435179 * 1.772454 / (2 * (109.988399388299 : ℝ))) * (1 + 0.001234845241) +
        8 / (12232 * 110.598372501587) + 0.125972995331 := by gcongr
    _ ≤ (0.164339952454 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439435179)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435132755) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284659621544) :
    parallelOracle 12232 0.011 xi bn cd ≤ 0.165370888464 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12232 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12232 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481594187 : ℝ) ≤ plow 12232 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.598372501587 : ℝ) ≤ √12232 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284659621544 : ℝ) / (2 * 0.560481594187 * 110.598372501587)) * 0.164339952454 +
        0.284659621544 ^ 2 / (2 * 0.560481594187 * 110.598372501587) := by gcongr
    _ ≤ (0.165370888464 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439435179) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435132755)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284659621544) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12232 12232 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481594187 : ℝ) ≤ plow 12232 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.598372501587 : ℝ) ≤ √12232 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12232 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12232 Θ 1.22 ≤ 0.011990235209 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.598372501587 := by gcongr <;> linarith
      _ ≤ (0.011990235209 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12232 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12232 12232 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12232 12232 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12232 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12232 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12232 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12232 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165370888464 + 0.011990235209 + (0.008646 : ℝ) *
        (1 + 2 * (0.284659621544 + 0.011990235209) / (0.560481594187 * 110.598372501587))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12232]

end BstLean.Part264b.N12232

/-! The original eight local profiles supply actual 12232 moment certificates. -/
namespace BstLean.Part264b.N12232
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12232 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053439435179 ∧
    0 ≤ bN 12232 BstLean.Part154.csC (groupTheta g) ∧ bN 12232 BstLean.Part154.csC (groupTheta g) ≤ 0.001435132755 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12232 12232 0.011
      (momentAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12232 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12232 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12232 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231169710774 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12232 0.011
      (momentAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12232 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12232
/-! The actual computed-centre upper energy formula at 12232. -/
namespace BstLean.Part264b.N12232
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12232

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12232
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12232 cell12232)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086995770084
  | 2 => 0.087969630805
  | 3 => 0.088946700965
  | 4 => 0.089929521654
  | 5 => 0.090921121554
  | 6 => 0.091925083280
  | 7 => 0.092945614893
  | 8 => 0.093987626449
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12232 12232 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12232 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12232

/-! Actual upper energy certificates on all 43 source endpoints at 12232. -/
namespace BstLean.Part264b.N12232
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12232 cell12232)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12232 (gMinus 12232) (1 - (cell12232 i).lower) ≤ 1 ∧
    energyUpper 12232 (gMinus 12232) (BstLean.Part211.gPlus 12232)
      (finiteEnergy 12232 12232 0.011) (1 - (cell12232 i).lower) ≤
      (cell12232 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12232) (by norm_num)
        (q := 1 - (cell12232 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12232,cell12232]) (by norm_num [scalarRow12232,cell12232])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12232,cell12232])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12232

/-! Source-cell containment and simple scalar guards at 12232. -/
namespace BstLean.Part264b.N12232
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12232 cell12232)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12232 ⟨10,by decide⟩).lower ∧ (cell12232 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12232 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12232 ⟨11,by decide⟩).lower ∧ (cell12232 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12232 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12232 ⟨12,by decide⟩).lower ∧ (cell12232 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12232 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12232 ⟨13,by decide⟩).lower ∧ (cell12232 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12232 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12232 ⟨14,by decide⟩).lower ∧ (cell12232 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12232 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12232 ⟨15,by decide⟩).lower ∧ (cell12232 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12232 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12232 ⟨16,by decide⟩).lower ∧ (cell12232 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12232 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12232 ⟨17,by decide⟩).lower ∧ (cell12232 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12232 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12232 ⟨18,by decide⟩).lower ∧ (cell12232 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12232 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12232 ⟨19,by decide⟩).lower ∧ (cell12232 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12232 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12232 ⟨20,by decide⟩).lower ∧ (cell12232 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12232 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12232 ⟨21,by decide⟩).lower ∧ (cell12232 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12232 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12232 ⟨22,by decide⟩).lower ∧ (cell12232 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12232 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12232 ⟨23,by decide⟩).lower ∧ (cell12232 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12232 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12232 ⟨24,by decide⟩).lower ∧ (cell12232 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12232 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12232 ⟨25,by decide⟩).lower ∧ (cell12232 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12232 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12232 ⟨26,by decide⟩).lower ∧ (cell12232 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12232 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12232 ⟨27,by decide⟩).lower ∧ (cell12232 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12232 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12232 ⟨28,by decide⟩).lower ∧ (cell12232 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12232 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12232 ⟨29,by decide⟩).lower ∧ (cell12232 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12232 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12232 ⟨30,by decide⟩).lower ∧ (cell12232 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12232 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12232 ⟨31,by decide⟩).lower ∧ (cell12232 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12232 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12232 ⟨32,by decide⟩).lower ∧ (cell12232 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12232 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12232 ⟨33,by decide⟩).lower ∧ (cell12232 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12232 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12232 ⟨34,by decide⟩).lower ∧ (cell12232 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12232 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12232 ⟨35,by decide⟩).lower ∧ (cell12232 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12232 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12232 ⟨36,by decide⟩).lower ∧ (cell12232 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12232 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12232 ⟨37,by decide⟩).lower ∧ (cell12232 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12232 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12232 ⟨38,by decide⟩).lower ∧ (cell12232 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12232 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12232 ⟨39,by decide⟩).lower ∧ (cell12232 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12232 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12232 ⟨40,by decide⟩).lower ∧ (cell12232 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12232 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12232 ⟨41,by decide⟩).lower ∧ (cell12232 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12232 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12232 ⟨42,by decide⟩).lower ∧ (cell12232 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12232 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12232 ⟨43,by decide⟩).lower ∧ (cell12232 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12232 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12232 ⟨44,by decide⟩).lower ∧ (cell12232 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12232 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12232 ⟨45,by decide⟩).lower ∧ (cell12232 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12232 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12232 ⟨46,by decide⟩).lower ∧ (cell12232 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12232 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12232 ⟨47,by decide⟩).lower ∧ (cell12232 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12232 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12232 ⟨48,by decide⟩).lower ∧ (cell12232 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12232 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12232 ⟨49,by decide⟩).lower ∧ (cell12232 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12232 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12232 ⟨50,by decide⟩).lower ∧ (cell12232 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12232 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12232 ⟨51,by decide⟩).lower ∧ (cell12232 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12232 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12232 ⟨52,by decide⟩).lower ∧ (cell12232 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12232 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12232 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12232 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12232,cell12232,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12232 i).lower ∧
    (cell12232 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12232 i).upper ≤ (0.532 : ℝ) ∧
    (cell12232 i).centre ≤ (0.1 : ℝ) ∧ (cell12232 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12232 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12232 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12232

/-! The local source numeric instances at 12232 have no network premises. -/
namespace BstLean.Part264b.N12232
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12232 cell12232)

noncomputable def sourceNumerics12232 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12232 (cell12232 i)
      scalarRow12232.M scalarRow12232.H scalarRow12232.xi := by
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
    energy_allowance := scalarRow12232.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12232]
    centre_nonneg := (scalarRow12232.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12232]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12232
/-! Actual 12233 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12233
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12233 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12233 12233 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12233.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12233 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12233 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12233 := gPlus_lower 12233
end BstLean.Part264b.N12233

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12233
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036492403587 : ℝ) ≤ wn 12233 := by
  have hn : √(12233 : ℝ) ≤ 110.602893271379 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12233 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.602893271379 ≤ 2 / √12233 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261669002 : ℝ) ≤ rhoBar 12233 BstLean.Part154.csC ∧
    rhoBar 12233 BstLean.Part154.csC ≤ 0.000261672588 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036492403587 : ℝ) / (1.295212 * 12233) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12233) := by gcongr
      _ ≤ (0.000261672588 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12233 BstLean.Part154.csC) ≤ 0.001046758825 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12233 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12233 BstLean.Part154.csC) (piBar (rhoBar 12233 BstLean.Part154.csC)) ≤ 0.000199867649 ∧
    cc1 (rhoBar 12233 BstLean.Part154.csC) (piBar (rhoBar 12233 BstLean.Part154.csC)) ≤ 0.000127177038 ∧
    cc2 (rhoBar 12233 BstLean.Part154.csC) ≤ 0.000073827155 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12233 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12233 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12233 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12233 BstLean.Part154.csC * nuR (rhoBar 12233 BstLean.Part154.csC)) ≤ 0.000523362294 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261672588 : ℝ) * 0.001046758825 := by gcongr
      _ ≤ (0.000523362294 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12233 BstLean.Part154.csC) * nuR (rhoBar 12233 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046758825 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12233 BstLean.Part154.csC) * rhoBar 12233 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261672588 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261672588 / 2 + 0.399 * 0.001046758825 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199867649 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523362294 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127177038 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261672588 / 1.414213562 := by gcongr
      _ ≤ (0.000073827155 : ℝ) := by norm_num

end BstLean.Part264b.N12233

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12233
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12233 BstLean.Part154.csC) (piBar (rhoBar 12233 BstLean.Part154.csC)) ≤ 1.72512E-7 := by
  have hr0 : 0 ≤ rhoBar 12233 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12233 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12233 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12233 BstLean.Part154.csC) (piBar (rhoBar 12233 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12233 BstLean.Part154.csC) (piBar (rhoBar 12233 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12233 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199867649 : ℝ) ^ 2 + 0.000127177038 ^ 2 + 3 * 0.000073827155 ^ 2 +
        2 * 0.797885 * 0.000199867649 * 0.000127177038 + 2 * 0.000199867649 * 0.000073827155 +
        4 * 0.797885 * 0.000127177038 * 0.000073827155 := by gcongr
    _ ≤ (1.72512E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12233 BstLean.Part154.csC Θ ≤ 0.002733370009 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12233 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12233 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12233 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12233 BstLean.Part154.csC) (piBar (rhoBar 12233 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12233 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72512E-7 / (0.000261669002 : ℝ) := by gcongr
    _ ≤ 0.002733370009 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12233 BstLean.Part154.csC Θ ≤ 0.003034823552 + 0.000690668797 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12233 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12233 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12233 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261672588 +
        (6863 / 10000) * 0.000261672588 * 12233 * 0.001046758825) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003034823552 + 0.000690668797 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12233 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12233 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12233 0.011 Θ ∧ gammaRatio 12233 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12233 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12233) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12233 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12233 0.011 Θ) :=
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
    badAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12233 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12233 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12233 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12233 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12233 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12233 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12233 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12233 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12233 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12233 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12233 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004134823552 + 0.003424038806 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12233

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12233
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12233 BstLean.Part154.csC) (piBar (rhoBar 12233 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12233 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12233 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12233 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12233 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12233 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12233 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12233 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12233 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12233 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12233 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12233 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12233 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053487700283 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12233) ≤ 0.010797525687 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12233 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010797525687 + 2 * 0.737676 / 12233) := by gcongr
    _ ≤ (0.053487700283 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12233 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12233

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12233
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481642933 : ℝ) ≤ plow 12233 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12233) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439043926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435019255) : eMP 12233 0.011 xi bn ≤ 0.001234745819 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12233 : ℝ) * (1 - 0.011))) ≤ 0.000610434669 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001435019255 / (12233 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610434669 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610434669 : ℝ) + 3.141593 * 0.053439043926 / (12233 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001234745819 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439043926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435019255) : PiBarMP 12233 12 0.011 xi bn ≤ 0.164333278230 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12233 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037881647998 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.992895225100 : ℝ) ≤ √((12233 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.602893271378 : ℝ) ≤ √12233 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12233) ≤ 0.125967846326 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037881647998 + 0.053439043926 * 1.772454 / (2 * (109.992895225100 : ℝ))) * (1 + 0.001234745819) +
        8 / (12233 * 110.602893271378) + 0.125967846326 := by gcongr
    _ ≤ (0.164333278230 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439043926)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435019255) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284656564809) :
    parallelOracle 12233 0.011 xi bn cd ≤ 0.165364138600 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12233 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12233 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481642933 : ℝ) ≤ plow 12233 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.602893271378 : ℝ) ≤ √12233 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284656564809 : ℝ) / (2 * 0.560481642933 * 110.602893271378)) * 0.164333278230 +
        0.284656564809 ^ 2 / (2 * 0.560481642933 * 110.602893271378) := by gcongr
    _ ≤ (0.165364138600 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053439043926) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001435019255)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284656564809) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12233 12233 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481642933 : ℝ) ≤ plow 12233 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.602893271378 : ℝ) ≤ √12233 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12233 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12233 Θ 1.22 ≤ 0.011989745122 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.602893271378 := by gcongr <;> linarith
      _ ≤ (0.011989745122 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12233 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12233 12233 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12233 12233 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12233 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12233 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12233 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12233 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165364138600 + 0.011989745122 + (0.008646 : ℝ) *
        (1 + 2 * (0.284656564809 + 0.011989745122) / (0.560481642933 * 110.602893271378))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12233]

end BstLean.Part264b.N12233

/-! The original eight local profiles supply actual 12233 moment certificates. -/
namespace BstLean.Part264b.N12233
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12233 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053439043926 ∧
    0 ≤ bN 12233 BstLean.Part154.csC (groupTheta g) ∧ bN 12233 BstLean.Part154.csC (groupTheta g) ≤ 0.001435019255 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12233 12233 0.011
      (momentAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12233 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12233 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12233 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231168864526 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12233 0.011
      (momentAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12233 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12233
/-! The actual computed-centre upper energy formula at 12233. -/
namespace BstLean.Part264b.N12233
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12233

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12233
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12233 cell12233)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086992198647
  | 2 => 0.087965977111
  | 3 => 0.088942950514
  | 4 => 0.089925656831
  | 5 => 0.090917121126
  | 6 => 0.091920921824
  | 7 => 0.092941262176
  | 8 => 0.093983046746
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12233 12233 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12233 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12233

/-! Actual upper energy certificates on all 43 source endpoints at 12233. -/
namespace BstLean.Part264b.N12233
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12233 cell12233)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12233 (gMinus 12233) (1 - (cell12233 i).lower) ≤ 1 ∧
    energyUpper 12233 (gMinus 12233) (BstLean.Part211.gPlus 12233)
      (finiteEnergy 12233 12233 0.011) (1 - (cell12233 i).lower) ≤
      (cell12233 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12233) (by norm_num)
        (q := 1 - (cell12233 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12233,cell12233]) (by norm_num [scalarRow12233,cell12233])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12233,cell12233])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12233

/-! Source-cell containment and simple scalar guards at 12233. -/
namespace BstLean.Part264b.N12233
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12233 cell12233)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12233 ⟨10,by decide⟩).lower ∧ (cell12233 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12233 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12233 ⟨11,by decide⟩).lower ∧ (cell12233 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12233 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12233 ⟨12,by decide⟩).lower ∧ (cell12233 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12233 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12233 ⟨13,by decide⟩).lower ∧ (cell12233 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12233 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12233 ⟨14,by decide⟩).lower ∧ (cell12233 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12233 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12233 ⟨15,by decide⟩).lower ∧ (cell12233 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12233 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12233 ⟨16,by decide⟩).lower ∧ (cell12233 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12233 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12233 ⟨17,by decide⟩).lower ∧ (cell12233 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12233 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12233 ⟨18,by decide⟩).lower ∧ (cell12233 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12233 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12233 ⟨19,by decide⟩).lower ∧ (cell12233 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12233 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12233 ⟨20,by decide⟩).lower ∧ (cell12233 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12233 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12233 ⟨21,by decide⟩).lower ∧ (cell12233 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12233 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12233 ⟨22,by decide⟩).lower ∧ (cell12233 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12233 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12233 ⟨23,by decide⟩).lower ∧ (cell12233 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12233 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12233 ⟨24,by decide⟩).lower ∧ (cell12233 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12233 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12233 ⟨25,by decide⟩).lower ∧ (cell12233 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12233 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12233 ⟨26,by decide⟩).lower ∧ (cell12233 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12233 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12233 ⟨27,by decide⟩).lower ∧ (cell12233 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12233 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12233 ⟨28,by decide⟩).lower ∧ (cell12233 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12233 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12233 ⟨29,by decide⟩).lower ∧ (cell12233 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12233 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12233 ⟨30,by decide⟩).lower ∧ (cell12233 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12233 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12233 ⟨31,by decide⟩).lower ∧ (cell12233 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12233 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12233 ⟨32,by decide⟩).lower ∧ (cell12233 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12233 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12233 ⟨33,by decide⟩).lower ∧ (cell12233 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12233 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12233 ⟨34,by decide⟩).lower ∧ (cell12233 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12233 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12233 ⟨35,by decide⟩).lower ∧ (cell12233 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12233 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12233 ⟨36,by decide⟩).lower ∧ (cell12233 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12233 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12233 ⟨37,by decide⟩).lower ∧ (cell12233 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12233 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12233 ⟨38,by decide⟩).lower ∧ (cell12233 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12233 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12233 ⟨39,by decide⟩).lower ∧ (cell12233 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12233 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12233 ⟨40,by decide⟩).lower ∧ (cell12233 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12233 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12233 ⟨41,by decide⟩).lower ∧ (cell12233 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12233 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12233 ⟨42,by decide⟩).lower ∧ (cell12233 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12233 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12233 ⟨43,by decide⟩).lower ∧ (cell12233 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12233 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12233 ⟨44,by decide⟩).lower ∧ (cell12233 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12233 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12233 ⟨45,by decide⟩).lower ∧ (cell12233 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12233 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12233 ⟨46,by decide⟩).lower ∧ (cell12233 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12233 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12233 ⟨47,by decide⟩).lower ∧ (cell12233 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12233 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12233 ⟨48,by decide⟩).lower ∧ (cell12233 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12233 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12233 ⟨49,by decide⟩).lower ∧ (cell12233 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12233 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12233 ⟨50,by decide⟩).lower ∧ (cell12233 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12233 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12233 ⟨51,by decide⟩).lower ∧ (cell12233 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12233 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12233 ⟨52,by decide⟩).lower ∧ (cell12233 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12233 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12233 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12233 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12233,cell12233,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12233 i).lower ∧
    (cell12233 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12233 i).upper ≤ (0.532 : ℝ) ∧
    (cell12233 i).centre ≤ (0.1 : ℝ) ∧ (cell12233 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12233 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12233 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12233

/-! The local source numeric instances at 12233 have no network premises. -/
namespace BstLean.Part264b.N12233
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12233 cell12233)

noncomputable def sourceNumerics12233 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12233 (cell12233 i)
      scalarRow12233.M scalarRow12233.H scalarRow12233.xi := by
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
    energy_allowance := scalarRow12233.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12233]
    centre_nonneg := (scalarRow12233.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12233]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12233
/-! Actual 12234 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12234
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12234 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12234 12234 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12234.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12234 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12234 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12234 := gPlus_lower 12234
end BstLean.Part264b.N12234

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12234
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036490898759 : ℝ) ≤ wn 12234 := by
  have hn : √(12234 : ℝ) ≤ 110.607413856396 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12234 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.607413856396 ≤ 2 / √12234 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261647234 : ℝ) ≤ rhoBar 12234 BstLean.Part154.csC ∧
    rhoBar 12234 BstLean.Part154.csC ≤ 0.000261651199 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036490898759 : ℝ) / (1.295212 * 12234) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12234) := by gcongr
      _ ≤ (0.000261651199 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12234 BstLean.Part154.csC) ≤ 0.001046673258 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12234 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12234 BstLean.Part154.csC) (piBar (rhoBar 12234 BstLean.Part154.csC)) ≤ 0.000199851312 ∧
    cc1 (rhoBar 12234 BstLean.Part154.csC) (piBar (rhoBar 12234 BstLean.Part154.csC)) ≤ 0.000127166642 ∧
    cc2 (rhoBar 12234 BstLean.Part154.csC) ≤ 0.000073821120 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12234 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12234 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12234 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12234 BstLean.Part154.csC * nuR (rhoBar 12234 BstLean.Part154.csC)) ≤ 0.000523319514 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261651199 : ℝ) * 0.001046673258 := by gcongr
      _ ≤ (0.000523319514 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12234 BstLean.Part154.csC) * nuR (rhoBar 12234 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046673258 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12234 BstLean.Part154.csC) * rhoBar 12234 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261651199 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261651199 / 2 + 0.399 * 0.001046673258 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199851312 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523319514 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127166642 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261651199 / 1.414213562 := by gcongr
      _ ≤ (0.000073821120 : ℝ) := by norm_num

end BstLean.Part264b.N12234

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12234
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12234 BstLean.Part154.csC) (piBar (rhoBar 12234 BstLean.Part154.csC)) ≤ 1.72484E-7 := by
  have hr0 : 0 ≤ rhoBar 12234 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12234 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12234 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12234 BstLean.Part154.csC) (piBar (rhoBar 12234 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12234 BstLean.Part154.csC) (piBar (rhoBar 12234 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12234 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199851312 : ℝ) ^ 2 + 0.000127166642 ^ 2 + 3 * 0.000073821120 ^ 2 +
        2 * 0.797885 * 0.000199851312 * 0.000127166642 + 2 * 0.000199851312 * 0.000073821120 +
        4 * 0.797885 * 0.000127166642 * 0.000073821120 := by gcongr
    _ ≤ (1.72484E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12234 BstLean.Part154.csC Θ ≤ 0.002733153731 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12234 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12234 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12234 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12234 BstLean.Part154.csC) (piBar (rhoBar 12234 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12234 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72484E-7 / (0.000261647234 : ℝ) := by gcongr
    _ ≤ 0.002733153731 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12234 BstLean.Part154.csC Θ ≤ 0.003034575471 + 0.000690612342 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12234 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12234 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12234 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261651199 +
        (6863 / 10000) * 0.000261651199 * 12234 * 0.001046673258) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003034575471 + 0.000690612342 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12234 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12234 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12234 0.011 Θ ∧ gammaRatio 12234 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12234 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12234) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12234 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12234 0.011 Θ) :=
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
    badAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12234 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12234 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12234 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12234 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12234 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12234 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12234 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12234 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12234 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12234 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12234 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004134575471 + 0.003423766073 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12234

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12234
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12234 BstLean.Part154.csC) (piBar (rhoBar 12234 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12234 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12234 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12234 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12234 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12234 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12234 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12234 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12234 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12234 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12234 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12234 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12234 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053485490064 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12234) ≤ 0.010797084386 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12234 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010797084386 + 2 * 0.737676 / 12234) := by gcongr
    _ ≤ (0.053485490064 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12234 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12234

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12234
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481691670 : ℝ) ≤ plow 12234 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12234) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053438652660)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434905709) : eMP 12234 0.011 xi bn ≤ 0.001234646387 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12234 : ℝ) * (1 - 0.011))) ≤ 0.000610385571 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001434905709 / (12234 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610385571 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610385571 : ℝ) + 3.141593 * 0.053438652660 / (12234 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001234646387 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053438652660)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434905709) : PiBarMP 12234 12 0.011 xi bn ≤ 0.164326603972 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12234 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037880149274 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.997390878147 : ℝ) ≤ √((12234 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.607413856395 : ℝ) ≤ √12234 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12234) ≤ 0.125962697952 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037880149274 + 0.053438652660 * 1.772454 / (2 * (109.997390878147 : ℝ))) * (1 + 0.001234646387) +
        8 / (12234 * 110.607413856395) + 0.125962697952 := by gcongr
    _ ≤ (0.164326603972 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053438652660)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434905709) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284653508311) :
    parallelOracle 12234 0.011 xi bn cd ≤ 0.165357388712 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12234 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12234 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481691670 : ℝ) ≤ plow 12234 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.607413856395 : ℝ) ≤ √12234 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284653508311 : ℝ) / (2 * 0.560481691670 * 110.607413856395)) * 0.164326603972 +
        0.284653508311 ^ 2 / (2 * 0.560481691670 * 110.607413856395) := by gcongr
    _ ≤ (0.165357388712 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053438652660) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434905709)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284653508311) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12234 12234 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481691670 : ℝ) ≤ plow 12234 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.607413856395 : ℝ) ≤ √12234 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12234 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12234 Θ 1.22 ≤ 0.011989255094 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.607413856395 := by gcongr <;> linarith
      _ ≤ (0.011989255094 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12234 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12234 12234 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12234 12234 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12234 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12234 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12234 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12234 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165357388712 + 0.011989255094 + (0.008646 : ℝ) *
        (1 + 2 * (0.284653508311 + 0.011989255094) / (0.560481691670 * 110.607413856395))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12234]

end BstLean.Part264b.N12234

/-! The original eight local profiles supply actual 12234 moment certificates. -/
namespace BstLean.Part264b.N12234
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12234 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053438652660 ∧
    0 ≤ bN 12234 BstLean.Part154.csC (groupTheta g) ∧ bN 12234 BstLean.Part154.csC (groupTheta g) ≤ 0.001434905709 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12234 12234 0.011
      (momentAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12234 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12234 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12234 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231168018247 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12234 0.011
      (momentAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12234 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12234
/-! The actual computed-centre upper energy formula at 12234. -/
namespace BstLean.Part264b.N12234
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12234

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12234
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12234 cell12234)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086988629000
  | 2 => 0.087962325288
  | 3 => 0.088939202034
  | 4 => 0.089921794104
  | 5 => 0.090913122943
  | 6 => 0.091916762796
  | 7 => 0.092936912106
  | 8 => 0.093978469948
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12234 12234 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12234 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12234

/-! Actual upper energy certificates on all 43 source endpoints at 12234. -/
namespace BstLean.Part264b.N12234
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12234 cell12234)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12234 (gMinus 12234) (1 - (cell12234 i).lower) ≤ 1 ∧
    energyUpper 12234 (gMinus 12234) (BstLean.Part211.gPlus 12234)
      (finiteEnergy 12234 12234 0.011) (1 - (cell12234 i).lower) ≤
      (cell12234 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12234) (by norm_num)
        (q := 1 - (cell12234 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12234,cell12234]) (by norm_num [scalarRow12234,cell12234])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12234,cell12234])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12234

/-! Source-cell containment and simple scalar guards at 12234. -/
namespace BstLean.Part264b.N12234
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12234 cell12234)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12234 ⟨10,by decide⟩).lower ∧ (cell12234 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12234 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12234 ⟨11,by decide⟩).lower ∧ (cell12234 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12234 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12234 ⟨12,by decide⟩).lower ∧ (cell12234 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12234 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12234 ⟨13,by decide⟩).lower ∧ (cell12234 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12234 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12234 ⟨14,by decide⟩).lower ∧ (cell12234 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12234 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12234 ⟨15,by decide⟩).lower ∧ (cell12234 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12234 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12234 ⟨16,by decide⟩).lower ∧ (cell12234 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12234 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12234 ⟨17,by decide⟩).lower ∧ (cell12234 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12234 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12234 ⟨18,by decide⟩).lower ∧ (cell12234 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12234 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12234 ⟨19,by decide⟩).lower ∧ (cell12234 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12234 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12234 ⟨20,by decide⟩).lower ∧ (cell12234 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12234 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12234 ⟨21,by decide⟩).lower ∧ (cell12234 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12234 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12234 ⟨22,by decide⟩).lower ∧ (cell12234 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12234 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12234 ⟨23,by decide⟩).lower ∧ (cell12234 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12234 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12234 ⟨24,by decide⟩).lower ∧ (cell12234 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12234 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12234 ⟨25,by decide⟩).lower ∧ (cell12234 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12234 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12234 ⟨26,by decide⟩).lower ∧ (cell12234 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12234 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12234 ⟨27,by decide⟩).lower ∧ (cell12234 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12234 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12234 ⟨28,by decide⟩).lower ∧ (cell12234 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12234 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12234 ⟨29,by decide⟩).lower ∧ (cell12234 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12234 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12234 ⟨30,by decide⟩).lower ∧ (cell12234 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12234 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12234 ⟨31,by decide⟩).lower ∧ (cell12234 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12234 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12234 ⟨32,by decide⟩).lower ∧ (cell12234 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12234 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12234 ⟨33,by decide⟩).lower ∧ (cell12234 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12234 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12234 ⟨34,by decide⟩).lower ∧ (cell12234 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12234 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12234 ⟨35,by decide⟩).lower ∧ (cell12234 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12234 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12234 ⟨36,by decide⟩).lower ∧ (cell12234 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12234 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12234 ⟨37,by decide⟩).lower ∧ (cell12234 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12234 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12234 ⟨38,by decide⟩).lower ∧ (cell12234 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12234 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12234 ⟨39,by decide⟩).lower ∧ (cell12234 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12234 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12234 ⟨40,by decide⟩).lower ∧ (cell12234 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12234 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12234 ⟨41,by decide⟩).lower ∧ (cell12234 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12234 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12234 ⟨42,by decide⟩).lower ∧ (cell12234 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12234 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12234 ⟨43,by decide⟩).lower ∧ (cell12234 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12234 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12234 ⟨44,by decide⟩).lower ∧ (cell12234 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12234 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12234 ⟨45,by decide⟩).lower ∧ (cell12234 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12234 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12234 ⟨46,by decide⟩).lower ∧ (cell12234 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12234 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12234 ⟨47,by decide⟩).lower ∧ (cell12234 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12234 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12234 ⟨48,by decide⟩).lower ∧ (cell12234 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12234 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12234 ⟨49,by decide⟩).lower ∧ (cell12234 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12234 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12234 ⟨50,by decide⟩).lower ∧ (cell12234 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12234 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12234 ⟨51,by decide⟩).lower ∧ (cell12234 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12234 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12234 ⟨52,by decide⟩).lower ∧ (cell12234 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12234 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12234 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12234 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12234,cell12234,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12234 i).lower ∧
    (cell12234 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12234 i).upper ≤ (0.532 : ℝ) ∧
    (cell12234 i).centre ≤ (0.1 : ℝ) ∧ (cell12234 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12234 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12234 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12234

/-! The local source numeric instances at 12234 have no network premises. -/
namespace BstLean.Part264b.N12234
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12234 cell12234)

noncomputable def sourceNumerics12234 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12234 (cell12234 i)
      scalarRow12234.M scalarRow12234.H scalarRow12234.xi := by
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
    energy_allowance := scalarRow12234.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12234]
    centre_nonneg := (scalarRow12234.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12234]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12234
/-! Actual 12235 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12235
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12235 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12235 12235 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12235.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12235 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12235 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12235 := gPlus_lower 12235
end BstLean.Part264b.N12235

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12235
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036489394117 : ℝ) ≤ wn 12235 := by
  have hn : √(12235 : ℝ) ≤ 110.611934256662 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12235 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.611934256662 ≤ 2 / √12235 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261625469 : ℝ) ≤ rhoBar 12235 BstLean.Part154.csC ∧
    rhoBar 12235 BstLean.Part154.csC ≤ 0.000261629813 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036489394117 : ℝ) / (1.295212 * 12235) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12235) := by gcongr
      _ ≤ (0.000261629813 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12235 BstLean.Part154.csC) ≤ 0.001046587703 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12235 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12235 BstLean.Part154.csC) (piBar (rhoBar 12235 BstLean.Part154.csC)) ≤ 0.000199834976 ∧
    cc1 (rhoBar 12235 BstLean.Part154.csC) (piBar (rhoBar 12235 BstLean.Part154.csC)) ≤ 0.000127156248 ∧
    cc2 (rhoBar 12235 BstLean.Part154.csC) ≤ 0.000073815086 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12235 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12235 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12235 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12235 BstLean.Part154.csC * nuR (rhoBar 12235 BstLean.Part154.csC)) ≤ 0.000523276739 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261629813 : ℝ) * 0.001046587703 := by gcongr
      _ ≤ (0.000523276739 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12235 BstLean.Part154.csC) * nuR (rhoBar 12235 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046587703 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12235 BstLean.Part154.csC) * rhoBar 12235 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261629813 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261629813 / 2 + 0.399 * 0.001046587703 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199834976 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523276739 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127156248 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261629813 / 1.414213562 := by gcongr
      _ ≤ (0.000073815086 : ℝ) := by norm_num

end BstLean.Part264b.N12235

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12235
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12235 BstLean.Part154.csC) (piBar (rhoBar 12235 BstLean.Part154.csC)) ≤ 1.72456E-7 := by
  have hr0 : 0 ≤ rhoBar 12235 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12235 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12235 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12235 BstLean.Part154.csC) (piBar (rhoBar 12235 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12235 BstLean.Part154.csC) (piBar (rhoBar 12235 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12235 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199834976 : ℝ) ^ 2 + 0.000127156248 ^ 2 + 3 * 0.000073815086 ^ 2 +
        2 * 0.797885 * 0.000199834976 * 0.000127156248 + 2 * 0.000199834976 * 0.000073815086 +
        4 * 0.797885 * 0.000127156248 * 0.000073815086 := by gcongr
    _ ≤ (1.72456E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12235 BstLean.Part154.csC Θ ≤ 0.002732937386 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12235 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12235 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12235 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12235 BstLean.Part154.csC) (piBar (rhoBar 12235 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12235 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72456E-7 / (0.000261625469 : ℝ) := by gcongr
    _ ≤ 0.002732937386 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12235 BstLean.Part154.csC Θ ≤ 0.003034327419 + 0.000690555895 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12235 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12235 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12235 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261629813 +
        (6863 / 10000) * 0.000261629813 * 12235 * 0.001046587703) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003034327419 + 0.000690555895 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12235 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12235 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12235 0.011 Θ ∧ gammaRatio 12235 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12235 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12235) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12235 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12235 0.011 Θ) :=
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
    badAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12235 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12235 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12235 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12235 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12235 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12235 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12235 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12235 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12235 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12235 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12235 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004134327419 + 0.003423493281 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12235

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12235
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12235 BstLean.Part154.csC) (piBar (rhoBar 12235 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12235 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12235 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12235 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12235 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12235 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12235 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12235 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12235 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12235 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12235 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12235 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12235 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053483280117 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12235) ≤ 0.010796643139 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12235 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010796643139 + 2 * 0.737676 / 12235) := by gcongr
    _ ≤ (0.053483280117 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12235 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12235

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12235
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481740400 : ℝ) ≤ plow 12235 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12235) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053438261392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434792128) : eMP 12235 0.011 xi bn ≤ 0.001234546948 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12235 : ℝ) * (1 - 0.011))) ≤ 0.000610336469 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001434792128 / (12235 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610336469 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610336469 : ℝ) + 3.141593 * 0.053438261392 / (12235 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001234546948 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053438261392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434792128) : PiBarMP 12235 12 0.011 xi bn ≤ 0.164319929826 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12235 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037878650029 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.001886347462 : ℝ) ≤ √((12235 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.611934256661 : ℝ) ≤ √12235 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12235) ≤ 0.125957550209 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037878650029 + 0.053438261392 * 1.772454 / (2 * (110.001886347462 : ℝ))) * (1 + 0.001234546948) +
        8 / (12235 * 110.611934256661) + 0.125957550209 := by gcongr
    _ ≤ (0.164319929826 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053438261392)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434792128) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284650452078) :
    parallelOracle 12235 0.011 xi bn cd ≤ 0.165350638947 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12235 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12235 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481740400 : ℝ) ≤ plow 12235 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.611934256661 : ℝ) ≤ √12235 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284650452078 : ℝ) / (2 * 0.560481740400 * 110.611934256661)) * 0.164319929826 +
        0.284650452078 ^ 2 / (2 * 0.560481740400 * 110.611934256661) := by gcongr
    _ ≤ (0.165350638947 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053438261392) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434792128)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284650452078) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12235 12235 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481740400 : ℝ) ≤ plow 12235 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.611934256661 : ℝ) ≤ √12235 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12235 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12235 Θ 1.22 ≤ 0.011988765127 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.611934256661 := by gcongr <;> linarith
      _ ≤ (0.011988765127 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12235 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12235 12235 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12235 12235 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12235 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12235 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12235 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12235 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165350638947 + 0.011988765127 + (0.008646 : ℝ) *
        (1 + 2 * (0.284650452078 + 0.011988765127) / (0.560481740400 * 110.611934256661))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12235]

end BstLean.Part264b.N12235

/-! The original eight local profiles supply actual 12235 moment certificates. -/
namespace BstLean.Part264b.N12235
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12235 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053438261392 ∧
    0 ≤ bN 12235 BstLean.Part154.csC (groupTheta g) ∧ bN 12235 BstLean.Part154.csC (groupTheta g) ≤ 0.001434792128 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12235 12235 0.011
      (momentAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12235 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12235 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12235 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231167171961 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12235 0.011
      (momentAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12235 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12235
/-! The actual computed-centre upper energy formula at 12235. -/
namespace BstLean.Part264b.N12235
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12235

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12235
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12235 cell12235)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086985061139
  | 2 => 0.087958675335
  | 3 => 0.088935455524
  | 4 => 0.089917933471
  | 5 => 0.090909127005
  | 6 => 0.091912606192
  | 7 => 0.092932564677
  | 8 => 0.093973896053
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12235 12235 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12235 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12235

/-! Actual upper energy certificates on all 43 source endpoints at 12235. -/
namespace BstLean.Part264b.N12235
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12235 cell12235)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12235 (gMinus 12235) (1 - (cell12235 i).lower) ≤ 1 ∧
    energyUpper 12235 (gMinus 12235) (BstLean.Part211.gPlus 12235)
      (finiteEnergy 12235 12235 0.011) (1 - (cell12235 i).lower) ≤
      (cell12235 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12235) (by norm_num)
        (q := 1 - (cell12235 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12235,cell12235]) (by norm_num [scalarRow12235,cell12235])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12235,cell12235])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12235

/-! Source-cell containment and simple scalar guards at 12235. -/
namespace BstLean.Part264b.N12235
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12235 cell12235)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12235 ⟨10,by decide⟩).lower ∧ (cell12235 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12235 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12235 ⟨11,by decide⟩).lower ∧ (cell12235 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12235 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12235 ⟨12,by decide⟩).lower ∧ (cell12235 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12235 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12235 ⟨13,by decide⟩).lower ∧ (cell12235 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12235 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12235 ⟨14,by decide⟩).lower ∧ (cell12235 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12235 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12235 ⟨15,by decide⟩).lower ∧ (cell12235 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12235 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12235 ⟨16,by decide⟩).lower ∧ (cell12235 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12235 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12235 ⟨17,by decide⟩).lower ∧ (cell12235 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12235 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12235 ⟨18,by decide⟩).lower ∧ (cell12235 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12235 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12235 ⟨19,by decide⟩).lower ∧ (cell12235 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12235 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12235 ⟨20,by decide⟩).lower ∧ (cell12235 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12235 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12235 ⟨21,by decide⟩).lower ∧ (cell12235 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12235 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12235 ⟨22,by decide⟩).lower ∧ (cell12235 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12235 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12235 ⟨23,by decide⟩).lower ∧ (cell12235 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12235 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12235 ⟨24,by decide⟩).lower ∧ (cell12235 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12235 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12235 ⟨25,by decide⟩).lower ∧ (cell12235 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12235 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12235 ⟨26,by decide⟩).lower ∧ (cell12235 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12235 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12235 ⟨27,by decide⟩).lower ∧ (cell12235 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12235 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12235 ⟨28,by decide⟩).lower ∧ (cell12235 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12235 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12235 ⟨29,by decide⟩).lower ∧ (cell12235 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12235 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12235 ⟨30,by decide⟩).lower ∧ (cell12235 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12235 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12235 ⟨31,by decide⟩).lower ∧ (cell12235 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12235 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12235 ⟨32,by decide⟩).lower ∧ (cell12235 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12235 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12235 ⟨33,by decide⟩).lower ∧ (cell12235 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12235 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12235 ⟨34,by decide⟩).lower ∧ (cell12235 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12235 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12235 ⟨35,by decide⟩).lower ∧ (cell12235 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12235 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12235 ⟨36,by decide⟩).lower ∧ (cell12235 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12235 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12235 ⟨37,by decide⟩).lower ∧ (cell12235 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12235 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12235 ⟨38,by decide⟩).lower ∧ (cell12235 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12235 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12235 ⟨39,by decide⟩).lower ∧ (cell12235 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12235 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12235 ⟨40,by decide⟩).lower ∧ (cell12235 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12235 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12235 ⟨41,by decide⟩).lower ∧ (cell12235 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12235 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12235 ⟨42,by decide⟩).lower ∧ (cell12235 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12235 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12235 ⟨43,by decide⟩).lower ∧ (cell12235 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12235 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12235 ⟨44,by decide⟩).lower ∧ (cell12235 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12235 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12235 ⟨45,by decide⟩).lower ∧ (cell12235 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12235 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12235 ⟨46,by decide⟩).lower ∧ (cell12235 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12235 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12235 ⟨47,by decide⟩).lower ∧ (cell12235 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12235 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12235 ⟨48,by decide⟩).lower ∧ (cell12235 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12235 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12235 ⟨49,by decide⟩).lower ∧ (cell12235 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12235 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12235 ⟨50,by decide⟩).lower ∧ (cell12235 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12235 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12235 ⟨51,by decide⟩).lower ∧ (cell12235 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12235 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12235 ⟨52,by decide⟩).lower ∧ (cell12235 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12235 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12235 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12235 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12235,cell12235,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12235 i).lower ∧
    (cell12235 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12235 i).upper ≤ (0.532 : ℝ) ∧
    (cell12235 i).centre ≤ (0.1 : ℝ) ∧ (cell12235 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12235 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12235 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12235

/-! The local source numeric instances at 12235 have no network premises. -/
namespace BstLean.Part264b.N12235
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12235 cell12235)

noncomputable def sourceNumerics12235 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12235 (cell12235 i)
      scalarRow12235.M scalarRow12235.H scalarRow12235.xi := by
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
    energy_allowance := scalarRow12235.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12235]
    centre_nonneg := (scalarRow12235.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12235]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12235
/-! Actual 12236 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12236
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12236 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12236 12236 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12236.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12236 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12236 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12236 := gPlus_lower 12236
end BstLean.Part264b.N12236

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12236
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036487889660 : ℝ) ≤ wn 12236 := by
  have hn : √(12236 : ℝ) ≤ 110.616454472199 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12236 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.616454472199 ≤ 2 / √12236 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261603708 : ℝ) ≤ rhoBar 12236 BstLean.Part154.csC ∧
    rhoBar 12236 BstLean.Part154.csC ≤ 0.000261608431 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036487889660 : ℝ) / (1.295212 * 12236) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12236) := by gcongr
      _ ≤ (0.000261608431 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12236 BstLean.Part154.csC) ≤ 0.001046502163 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12236 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12236 BstLean.Part154.csC) (piBar (rhoBar 12236 BstLean.Part154.csC)) ≤ 0.000199818643 ∧
    cc1 (rhoBar 12236 BstLean.Part154.csC) (piBar (rhoBar 12236 BstLean.Part154.csC)) ≤ 0.000127145856 ∧
    cc2 (rhoBar 12236 BstLean.Part154.csC) ≤ 0.000073809054 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12236 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12236 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12236 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12236 BstLean.Part154.csC * nuR (rhoBar 12236 BstLean.Part154.csC)) ≤ 0.000523233972 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261608431 : ℝ) * 0.001046502163 := by gcongr
      _ ≤ (0.000523233972 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12236 BstLean.Part154.csC) * nuR (rhoBar 12236 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046502163 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12236 BstLean.Part154.csC) * rhoBar 12236 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261608431 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261608431 / 2 + 0.399 * 0.001046502163 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199818643 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523233972 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127145856 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261608431 / 1.414213562 := by gcongr
      _ ≤ (0.000073809054 : ℝ) := by norm_num

end BstLean.Part264b.N12236

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12236
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12236 BstLean.Part154.csC) (piBar (rhoBar 12236 BstLean.Part154.csC)) ≤ 1.72428E-7 := by
  have hr0 : 0 ≤ rhoBar 12236 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12236 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12236 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12236 BstLean.Part154.csC) (piBar (rhoBar 12236 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12236 BstLean.Part154.csC) (piBar (rhoBar 12236 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12236 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199818643 : ℝ) ^ 2 + 0.000127145856 ^ 2 + 3 * 0.000073809054 ^ 2 +
        2 * 0.797885 * 0.000199818643 * 0.000127145856 + 2 * 0.000199818643 * 0.000073809054 +
        4 * 0.797885 * 0.000127145856 * 0.000073809054 := by gcongr
    _ ≤ (1.72428E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12236 BstLean.Part154.csC Θ ≤ 0.002732720962 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12236 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12236 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12236 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12236 BstLean.Part154.csC) (piBar (rhoBar 12236 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12236 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72428E-7 / (0.000261603708 : ℝ) := by gcongr
    _ ≤ 0.002732720962 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12236 BstLean.Part154.csC Θ ≤ 0.003034079416 + 0.000690499459 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12236 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12236 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12236 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261608431 +
        (6863 / 10000) * 0.000261608431 * 12236 * 0.001046502163) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003034079416 + 0.000690499459 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12236 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12236 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12236 0.011 Θ ∧ gammaRatio 12236 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12236 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12236) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12236 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12236 0.011 Θ) :=
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
    badAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12236 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12236 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12236 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12236 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12236 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12236 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12236 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12236 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12236 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12236 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12236 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004134079416 + 0.003423220421 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12236

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12236
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12236 BstLean.Part154.csC) (piBar (rhoBar 12236 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12236 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12236 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12236 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12236 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12236 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12236 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12236 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12236 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12236 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12236 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12236 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12236 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053481070447 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12236) ≤ 0.010796201947 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12236 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010796201947 + 2 * 0.737676 / 12236) := by gcongr
    _ ≤ (0.053481070447 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12236 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12236

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12236
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481789122 : ℝ) ≤ plow 12236 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12236) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437870138)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434678506) : eMP 12236 0.011 xi bn ≤ 0.001234447498 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12236 : ℝ) * (1 - 0.011))) ≤ 0.000610287362 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001434678506 / (12236 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610287362 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610287362 : ℝ) + 3.141593 * 0.053437870138 / (12236 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001234447498 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437870138)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434678506) : PiBarMP 12236 12 0.011 xi bn ≤ 0.164313255712 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12236 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037877150184 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.006381633067 : ℝ) ≤ √((12236 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.616454472198 : ℝ) ≤ √12236 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12236) ≤ 0.125952403097 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037877150184 + 0.053437870138 * 1.772454 / (2 * (110.006381633067 : ℝ))) * (1 + 0.001234447498) +
        8 / (12236 * 110.616454472198) + 0.125952403097 := by gcongr
    _ ≤ (0.164313255712 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437870138)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434678506) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284647396148) :
    parallelOracle 12236 0.011 xi bn cd ≤ 0.165343889223 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12236 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12236 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481789122 : ℝ) ≤ plow 12236 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.616454472198 : ℝ) ≤ √12236 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284647396148 : ℝ) / (2 * 0.560481789122 * 110.616454472198)) * 0.164313255712 +
        0.284647396148 ^ 2 / (2 * 0.560481789122 * 110.616454472198) := by gcongr
    _ ≤ (0.165343889223 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437870138) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434678506)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284647396148) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12236 12236 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481789122 : ℝ) ≤ plow 12236 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.616454472198 : ℝ) ≤ √12236 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12236 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12236 Θ 1.22 ≤ 0.011988275220 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.616454472198 := by gcongr <;> linarith
      _ ≤ (0.011988275220 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12236 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12236 12236 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12236 12236 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12236 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12236 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12236 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12236 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165343889223 + 0.011988275220 + (0.008646 : ℝ) *
        (1 + 2 * (0.284647396148 + 0.011988275220) / (0.560481789122 * 110.616454472198))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12236]

end BstLean.Part264b.N12236

/-! The original eight local profiles supply actual 12236 moment certificates. -/
namespace BstLean.Part264b.N12236
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12236 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053437870138 ∧
    0 ≤ bN 12236 BstLean.Part154.csC (groupTheta g) ∧ bN 12236 BstLean.Part154.csC (groupTheta g) ≤ 0.001434678506 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12236 12236 0.011
      (momentAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12236 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12236 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12236 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231166325701 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12236 0.011
      (momentAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12236 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12236
/-! The actual computed-centre upper energy formula at 12236. -/
namespace BstLean.Part264b.N12236
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12236

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12236
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12236 cell12236)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086981495064
  | 2 => 0.087955027248
  | 3 => 0.088931710982
  | 4 => 0.089914074928
  | 5 => 0.090905133306
  | 6 => 0.091908452010
  | 7 => 0.092928219888
  | 8 => 0.093969325058
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12236 12236 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12236 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12236

/-! Actual upper energy certificates on all 43 source endpoints at 12236. -/
namespace BstLean.Part264b.N12236
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12236 cell12236)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12236 (gMinus 12236) (1 - (cell12236 i).lower) ≤ 1 ∧
    energyUpper 12236 (gMinus 12236) (BstLean.Part211.gPlus 12236)
      (finiteEnergy 12236 12236 0.011) (1 - (cell12236 i).lower) ≤
      (cell12236 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12236) (by norm_num)
        (q := 1 - (cell12236 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12236,cell12236]) (by norm_num [scalarRow12236,cell12236])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12236,cell12236])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12236

/-! Source-cell containment and simple scalar guards at 12236. -/
namespace BstLean.Part264b.N12236
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12236 cell12236)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12236 ⟨10,by decide⟩).lower ∧ (cell12236 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12236 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12236 ⟨11,by decide⟩).lower ∧ (cell12236 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12236 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12236 ⟨12,by decide⟩).lower ∧ (cell12236 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12236 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12236 ⟨13,by decide⟩).lower ∧ (cell12236 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12236 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12236 ⟨14,by decide⟩).lower ∧ (cell12236 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12236 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12236 ⟨15,by decide⟩).lower ∧ (cell12236 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12236 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12236 ⟨16,by decide⟩).lower ∧ (cell12236 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12236 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12236 ⟨17,by decide⟩).lower ∧ (cell12236 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12236 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12236 ⟨18,by decide⟩).lower ∧ (cell12236 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12236 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12236 ⟨19,by decide⟩).lower ∧ (cell12236 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12236 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12236 ⟨20,by decide⟩).lower ∧ (cell12236 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12236 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12236 ⟨21,by decide⟩).lower ∧ (cell12236 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12236 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12236 ⟨22,by decide⟩).lower ∧ (cell12236 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12236 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12236 ⟨23,by decide⟩).lower ∧ (cell12236 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12236 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12236 ⟨24,by decide⟩).lower ∧ (cell12236 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12236 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12236 ⟨25,by decide⟩).lower ∧ (cell12236 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12236 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12236 ⟨26,by decide⟩).lower ∧ (cell12236 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12236 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12236 ⟨27,by decide⟩).lower ∧ (cell12236 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12236 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12236 ⟨28,by decide⟩).lower ∧ (cell12236 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12236 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12236 ⟨29,by decide⟩).lower ∧ (cell12236 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12236 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12236 ⟨30,by decide⟩).lower ∧ (cell12236 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12236 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12236 ⟨31,by decide⟩).lower ∧ (cell12236 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12236 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12236 ⟨32,by decide⟩).lower ∧ (cell12236 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12236 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12236 ⟨33,by decide⟩).lower ∧ (cell12236 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12236 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12236 ⟨34,by decide⟩).lower ∧ (cell12236 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12236 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12236 ⟨35,by decide⟩).lower ∧ (cell12236 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12236 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12236 ⟨36,by decide⟩).lower ∧ (cell12236 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12236 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12236 ⟨37,by decide⟩).lower ∧ (cell12236 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12236 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12236 ⟨38,by decide⟩).lower ∧ (cell12236 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12236 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12236 ⟨39,by decide⟩).lower ∧ (cell12236 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12236 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12236 ⟨40,by decide⟩).lower ∧ (cell12236 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12236 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12236 ⟨41,by decide⟩).lower ∧ (cell12236 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12236 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12236 ⟨42,by decide⟩).lower ∧ (cell12236 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12236 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12236 ⟨43,by decide⟩).lower ∧ (cell12236 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12236 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12236 ⟨44,by decide⟩).lower ∧ (cell12236 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12236 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12236 ⟨45,by decide⟩).lower ∧ (cell12236 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12236 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12236 ⟨46,by decide⟩).lower ∧ (cell12236 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12236 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12236 ⟨47,by decide⟩).lower ∧ (cell12236 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12236 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12236 ⟨48,by decide⟩).lower ∧ (cell12236 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12236 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12236 ⟨49,by decide⟩).lower ∧ (cell12236 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12236 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12236 ⟨50,by decide⟩).lower ∧ (cell12236 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12236 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12236 ⟨51,by decide⟩).lower ∧ (cell12236 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12236 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12236 ⟨52,by decide⟩).lower ∧ (cell12236 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12236 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12236 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12236 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12236,cell12236,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12236 i).lower ∧
    (cell12236 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12236 i).upper ≤ (0.532 : ℝ) ∧
    (cell12236 i).centre ≤ (0.1 : ℝ) ∧ (cell12236 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12236 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12236 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12236

/-! The local source numeric instances at 12236 have no network premises. -/
namespace BstLean.Part264b.N12236
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12236 cell12236)

noncomputable def sourceNumerics12236 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12236 (cell12236 i)
      scalarRow12236.M scalarRow12236.H scalarRow12236.xi := by
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
    energy_allowance := scalarRow12236.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12236]
    centre_nonneg := (scalarRow12236.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12236]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12236
/-! Actual 12237 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12237
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12237 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12237 12237 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12237.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12237 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12237 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12237 := gPlus_lower 12237
end BstLean.Part264b.N12237

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12237
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036486385389 : ℝ) ≤ wn 12237 := by
  have hn : √(12237 : ℝ) ≤ 110.620974503030 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12237 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.620974503030 ≤ 2 / √12237 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261581950 : ℝ) ≤ rhoBar 12237 BstLean.Part154.csC ∧
    rhoBar 12237 BstLean.Part154.csC ≤ 0.000261587053 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036486385389 : ℝ) / (1.295212 * 12237) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12237) := by gcongr
      _ ≤ (0.000261587053 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12237 BstLean.Part154.csC) ≤ 0.001046416640 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12237 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12237 BstLean.Part154.csC) (piBar (rhoBar 12237 BstLean.Part154.csC)) ≤ 0.000199802314 ∧
    cc1 (rhoBar 12237 BstLean.Part154.csC) (piBar (rhoBar 12237 BstLean.Part154.csC)) ≤ 0.000127135465 ∧
    cc2 (rhoBar 12237 BstLean.Part154.csC) ≤ 0.000073803022 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12237 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12237 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12237 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12237 BstLean.Part154.csC * nuR (rhoBar 12237 BstLean.Part154.csC)) ≤ 0.000523191213 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261587053 : ℝ) * 0.001046416640 := by gcongr
      _ ≤ (0.000523191213 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12237 BstLean.Part154.csC) * nuR (rhoBar 12237 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046416640 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12237 BstLean.Part154.csC) * rhoBar 12237 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261587053 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261587053 / 2 + 0.399 * 0.001046416640 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199802314 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523191213 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127135465 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261587053 / 1.414213562 := by gcongr
      _ ≤ (0.000073803022 : ℝ) := by norm_num

end BstLean.Part264b.N12237

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12237
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12237 BstLean.Part154.csC) (piBar (rhoBar 12237 BstLean.Part154.csC)) ≤ 1.72399E-7 := by
  have hr0 : 0 ≤ rhoBar 12237 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12237 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12237 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12237 BstLean.Part154.csC) (piBar (rhoBar 12237 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12237 BstLean.Part154.csC) (piBar (rhoBar 12237 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12237 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199802314 : ℝ) ^ 2 + 0.000127135465 ^ 2 + 3 * 0.000073803022 ^ 2 +
        2 * 0.797885 * 0.000199802314 * 0.000127135465 + 2 * 0.000199802314 * 0.000073803022 +
        4 * 0.797885 * 0.000127135465 * 0.000073803022 := by gcongr
    _ ≤ (1.72399E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12237 BstLean.Part154.csC Θ ≤ 0.002732488622 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12237 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12237 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12237 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12237 BstLean.Part154.csC) (piBar (rhoBar 12237 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12237 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72399E-7 / (0.000261581950 : ℝ) := by gcongr
    _ ≤ 0.002732488622 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12237 BstLean.Part154.csC Θ ≤ 0.003033831468 + 0.000690443033 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12237 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12237 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12237 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261587053 +
        (6863 / 10000) * 0.000261587053 * 12237 * 0.001046416640) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003033831468 + 0.000690443033 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12237 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12237 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12237 0.011 Θ ∧ gammaRatio 12237 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12237 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12237) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12237 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12237 0.011 Θ) :=
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
    badAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12237 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12237 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12237 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12237 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12237 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12237 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12237 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12237 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12237 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12237 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12237 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004133831468 + 0.003422931655 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12237

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12237
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12237 BstLean.Part154.csC) (piBar (rhoBar 12237 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12237 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12237 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12237 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12237 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12237 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12237 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12237 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12237 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12237 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12237 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12237 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12237 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053478861045 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12237) ≤ 0.010795760808 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12237 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010795760808 + 2 * 0.737676 / 12237) := by gcongr
    _ ≤ (0.053478861045 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12237 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12237

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12237
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481837836 : ℝ) ≤ plow 12237 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12237) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437470587)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434556527) : eMP 12237 0.011 xi bn ≤ 0.001234344501 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12237 : ℝ) * (1 - 0.011))) ≤ 0.000610236482 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001434556527 / (12237 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610236482 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610236482 : ℝ) + 3.141593 * 0.053437470587 / (12237 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001234344501 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437470587)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434556527) : PiBarMP 12237 12 0.011 xi bn ≤ 0.164306471512 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12237 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037875539957 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.010876734984 : ℝ) ≤ √((12237 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.620974503029 : ℝ) ≤ √12237 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12237) ≤ 0.125947256616 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037875539957 + 0.053437470587 * 1.772454 / (2 * (110.010876734984 : ℝ))) * (1 + 0.001234344501) +
        8 / (12237 * 110.620974503029) + 0.125947256616 := by gcongr
    _ ≤ (0.164306471512 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437470587)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434556527) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284644322538) :
    parallelOracle 12237 0.011 xi bn cd ≤ 0.165337029064 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12237 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12237 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481837836 : ℝ) ≤ plow 12237 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.620974503029 : ℝ) ≤ √12237 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284644322538 : ℝ) / (2 * 0.560481837836 * 110.620974503029)) * 0.164306471512 +
        0.284644322538 ^ 2 / (2 * 0.560481837836 * 110.620974503029) := by gcongr
    _ ≤ (0.165337029064 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437470587) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434556527)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284644322538) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12237 12237 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481837836 : ℝ) ≤ plow 12237 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.620974503029 : ℝ) ≤ √12237 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12237 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12237 Θ 1.22 ≤ 0.011987785373 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.620974503029 := by gcongr <;> linarith
      _ ≤ (0.011987785373 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12237 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12237 12237 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12237 12237 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12237 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12237 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12237 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12237 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165337029064 + 0.011987785373 + (0.008646 : ℝ) *
        (1 + 2 * (0.284644322538 + 0.011987785373) / (0.560481837836 * 110.620974503029))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12237]

end BstLean.Part264b.N12237

/-! The original eight local profiles supply actual 12237 moment certificates. -/
namespace BstLean.Part264b.N12237
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12237 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053437470587 ∧
    0 ≤ bN 12237 BstLean.Part154.csC (groupTheta g) ∧ bN 12237 BstLean.Part154.csC (groupTheta g) ≤ 0.001434556527 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12237 12237 0.011
      (momentAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12237 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12237 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12237 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231165461493 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12237 0.011
      (momentAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12237 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12237
/-! The actual computed-centre upper energy formula at 12237. -/
namespace BstLean.Part264b.N12237
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12237

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12237
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12237 cell12237)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086977930771
  | 2 => 0.087951381026
  | 3 => 0.088927968405
  | 4 => 0.089910218474
  | 5 => 0.090901141847
  | 6 => 0.091904300248
  | 7 => 0.092923877736
  | 8 => 0.093964756958
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12237 12237 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12237 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12237

/-! Actual upper energy certificates on all 43 source endpoints at 12237. -/
namespace BstLean.Part264b.N12237
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12237 cell12237)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12237 (gMinus 12237) (1 - (cell12237 i).lower) ≤ 1 ∧
    energyUpper 12237 (gMinus 12237) (BstLean.Part211.gPlus 12237)
      (finiteEnergy 12237 12237 0.011) (1 - (cell12237 i).lower) ≤
      (cell12237 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12237) (by norm_num)
        (q := 1 - (cell12237 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12237,cell12237]) (by norm_num [scalarRow12237,cell12237])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12237,cell12237])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12237

/-! Source-cell containment and simple scalar guards at 12237. -/
namespace BstLean.Part264b.N12237
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12237 cell12237)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12237 ⟨10,by decide⟩).lower ∧ (cell12237 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12237 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12237 ⟨11,by decide⟩).lower ∧ (cell12237 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12237 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12237 ⟨12,by decide⟩).lower ∧ (cell12237 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12237 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12237 ⟨13,by decide⟩).lower ∧ (cell12237 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12237 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12237 ⟨14,by decide⟩).lower ∧ (cell12237 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12237 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12237 ⟨15,by decide⟩).lower ∧ (cell12237 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12237 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12237 ⟨16,by decide⟩).lower ∧ (cell12237 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12237 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12237 ⟨17,by decide⟩).lower ∧ (cell12237 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12237 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12237 ⟨18,by decide⟩).lower ∧ (cell12237 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12237 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12237 ⟨19,by decide⟩).lower ∧ (cell12237 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12237 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12237 ⟨20,by decide⟩).lower ∧ (cell12237 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12237 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12237 ⟨21,by decide⟩).lower ∧ (cell12237 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12237 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12237 ⟨22,by decide⟩).lower ∧ (cell12237 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12237 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12237 ⟨23,by decide⟩).lower ∧ (cell12237 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12237 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12237 ⟨24,by decide⟩).lower ∧ (cell12237 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12237 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12237 ⟨25,by decide⟩).lower ∧ (cell12237 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12237 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12237 ⟨26,by decide⟩).lower ∧ (cell12237 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12237 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12237 ⟨27,by decide⟩).lower ∧ (cell12237 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12237 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12237 ⟨28,by decide⟩).lower ∧ (cell12237 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12237 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12237 ⟨29,by decide⟩).lower ∧ (cell12237 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12237 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12237 ⟨30,by decide⟩).lower ∧ (cell12237 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12237 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12237 ⟨31,by decide⟩).lower ∧ (cell12237 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12237 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12237 ⟨32,by decide⟩).lower ∧ (cell12237 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12237 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12237 ⟨33,by decide⟩).lower ∧ (cell12237 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12237 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12237 ⟨34,by decide⟩).lower ∧ (cell12237 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12237 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12237 ⟨35,by decide⟩).lower ∧ (cell12237 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12237 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12237 ⟨36,by decide⟩).lower ∧ (cell12237 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12237 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12237 ⟨37,by decide⟩).lower ∧ (cell12237 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12237 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12237 ⟨38,by decide⟩).lower ∧ (cell12237 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12237 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12237 ⟨39,by decide⟩).lower ∧ (cell12237 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12237 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12237 ⟨40,by decide⟩).lower ∧ (cell12237 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12237 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12237 ⟨41,by decide⟩).lower ∧ (cell12237 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12237 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12237 ⟨42,by decide⟩).lower ∧ (cell12237 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12237 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12237 ⟨43,by decide⟩).lower ∧ (cell12237 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12237 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12237 ⟨44,by decide⟩).lower ∧ (cell12237 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12237 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12237 ⟨45,by decide⟩).lower ∧ (cell12237 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12237 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12237 ⟨46,by decide⟩).lower ∧ (cell12237 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12237 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12237 ⟨47,by decide⟩).lower ∧ (cell12237 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12237 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12237 ⟨48,by decide⟩).lower ∧ (cell12237 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12237 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12237 ⟨49,by decide⟩).lower ∧ (cell12237 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12237 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12237 ⟨50,by decide⟩).lower ∧ (cell12237 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12237 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12237 ⟨51,by decide⟩).lower ∧ (cell12237 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12237 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12237 ⟨52,by decide⟩).lower ∧ (cell12237 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12237 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12237 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12237 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12237,cell12237,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12237 i).lower ∧
    (cell12237 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12237 i).upper ≤ (0.532 : ℝ) ∧
    (cell12237 i).centre ≤ (0.1 : ℝ) ∧ (cell12237 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12237 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12237 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12237

/-! The local source numeric instances at 12237 have no network premises. -/
namespace BstLean.Part264b.N12237
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12237 cell12237)

noncomputable def sourceNumerics12237 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12237 (cell12237 i)
      scalarRow12237.M scalarRow12237.H scalarRow12237.xi := by
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
    energy_allowance := scalarRow12237.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12237]
    centre_nonneg := (scalarRow12237.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12237]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12237
/-! Actual 12238 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12238
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12238 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12238 12238 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12238.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12238 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12238 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12238 := gPlus_lower 12238
end BstLean.Part264b.N12238

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12238
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036484881303 : ℝ) ≤ wn 12238 := by
  have hn : √(12238 : ℝ) ≤ 110.625494349178 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12238 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.625494349178 ≤ 2 / √12238 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261560196 : ℝ) ≤ rhoBar 12238 BstLean.Part154.csC ∧
    rhoBar 12238 BstLean.Part154.csC ≤ 0.000261565678 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036484881303 : ℝ) / (1.295212 * 12238) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12238) := by gcongr
      _ ≤ (0.000261565678 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12238 BstLean.Part154.csC) ≤ 0.001046331129 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12238 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12238 BstLean.Part154.csC) (piBar (rhoBar 12238 BstLean.Part154.csC)) ≤ 0.000199785987 ∧
    cc1 (rhoBar 12238 BstLean.Part154.csC) (piBar (rhoBar 12238 BstLean.Part154.csC)) ≤ 0.000127125076 ∧
    cc2 (rhoBar 12238 BstLean.Part154.csC) ≤ 0.000073796992 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12238 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12238 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12238 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12238 BstLean.Part154.csC * nuR (rhoBar 12238 BstLean.Part154.csC)) ≤ 0.000523148460 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261565678 : ℝ) * 0.001046331129 := by gcongr
      _ ≤ (0.000523148460 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12238 BstLean.Part154.csC) * nuR (rhoBar 12238 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046331129 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12238 BstLean.Part154.csC) * rhoBar 12238 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261565678 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261565678 / 2 + 0.399 * 0.001046331129 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199785987 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523148460 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127125076 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261565678 / 1.414213562 := by gcongr
      _ ≤ (0.000073796992 : ℝ) := by norm_num

end BstLean.Part264b.N12238

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12238
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12238 BstLean.Part154.csC) (piBar (rhoBar 12238 BstLean.Part154.csC)) ≤ 1.72371E-7 := by
  have hr0 : 0 ≤ rhoBar 12238 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12238 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12238 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12238 BstLean.Part154.csC) (piBar (rhoBar 12238 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12238 BstLean.Part154.csC) (piBar (rhoBar 12238 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12238 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199785987 : ℝ) ^ 2 + 0.000127125076 ^ 2 + 3 * 0.000073796992 ^ 2 +
        2 * 0.797885 * 0.000199785987 * 0.000127125076 + 2 * 0.000199785987 * 0.000073796992 +
        4 * 0.797885 * 0.000127125076 * 0.000073796992 := by gcongr
    _ ≤ (1.72371E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12238 BstLean.Part154.csC Θ ≤ 0.002732272052 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12238 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12238 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12238 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12238 BstLean.Part154.csC) (piBar (rhoBar 12238 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12238 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72371E-7 / (0.000261560196 : ℝ) := by gcongr
    _ ≤ 0.002732272052 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12238 BstLean.Part154.csC Θ ≤ 0.003033583550 + 0.000690386615 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12238 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12238 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12238 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261565678 +
        (6863 / 10000) * 0.000261565678 * 12238 * 0.001046331129) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003033583550 + 0.000690386615 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12238 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12238 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12238 0.011 Θ ∧ gammaRatio 12238 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12238 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12238) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12238 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12238 0.011 Θ) :=
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
    badAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12238 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12238 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12238 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12238 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12238 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12238 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12238 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12238 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12238 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12238 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12238 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004133583550 + 0.003422658667 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12238

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12238
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12238 BstLean.Part154.csC) (piBar (rhoBar 12238 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12238 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12238 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12238 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12238 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12238 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12238 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12238 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12238 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12238 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12238 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12238 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12238 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053476651920 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12238) ≤ 0.010795319724 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12238 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010795319724 + 2 * 0.737676 / 12238) := by gcongr
    _ ≤ (0.053476651920 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12238 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12238

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12238
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481886541 : ℝ) ≤ plow 12238 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12238) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437079351)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434442828) : eMP 12238 0.011 xi bn ≤ 0.001234245036 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12238 : ℝ) * (1 - 0.011))) ≤ 0.000610187367 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001434442828 / (12238 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610187367 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610187367 : ℝ) + 3.141593 * 0.053437079351 / (12238 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001234245036 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437079351)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434442828) : PiBarMP 12238 12 0.011 xi bn ≤ 0.164299797523 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12238 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037874038972 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.015371653237 : ℝ) ≤ √((12238 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.625494349177 : ℝ) ≤ √12238 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12238) ≤ 0.125942110765 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037874038972 + 0.053437079351 * 1.772454 / (2 * (110.015371653237 : ℝ))) * (1 + 0.001234245036) +
        8 / (12238 * 110.625494349177) + 0.125942110765 := by gcongr
    _ ≤ (0.164299797523 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437079351)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434442828) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284641267186) :
    parallelOracle 12238 0.011 xi bn cd ≤ 0.165330279486 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12238 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12238 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481886541 : ℝ) ≤ plow 12238 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.625494349177 : ℝ) ≤ √12238 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284641267186 : ℝ) / (2 * 0.560481886541 * 110.625494349177)) * 0.164299797523 +
        0.284641267186 ^ 2 / (2 * 0.560481886541 * 110.625494349177) := by gcongr
    _ ≤ (0.165330279486 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053437079351) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434442828)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284641267186) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12238 12238 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481886541 : ℝ) ≤ plow 12238 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.625494349177 : ℝ) ≤ √12238 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12238 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12238 Θ 1.22 ≤ 0.011987295585 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.625494349177 := by gcongr <;> linarith
      _ ≤ (0.011987295585 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12238 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12238 12238 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12238 12238 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12238 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12238 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12238 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12238 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165330279486 + 0.011987295585 + (0.008646 : ℝ) *
        (1 + 2 * (0.284641267186 + 0.011987295585) / (0.560481886541 * 110.625494349177))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12238]

end BstLean.Part264b.N12238

/-! The original eight local profiles supply actual 12238 moment certificates. -/
namespace BstLean.Part264b.N12238
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12238 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053437079351 ∧
    0 ≤ bN 12238 BstLean.Part154.csC (groupTheta g) ∧ bN 12238 BstLean.Part154.csC (groupTheta g) ≤ 0.001434442828 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12238 12238 0.011
      (momentAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12238 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12238 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12238 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231164615266 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12238 0.011
      (momentAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12238 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12238
/-! The actual computed-centre upper energy formula at 12238. -/
namespace BstLean.Part264b.N12238
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12238

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12238
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12238 cell12238)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086974368259
  | 2 => 0.087947736666
  | 3 => 0.088924227792
  | 4 => 0.089906364106
  | 5 => 0.090897152622
  | 6 => 0.091900150901
  | 7 => 0.092919538216
  | 8 => 0.093960191751
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12238 12238 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12238 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12238

/-! Actual upper energy certificates on all 43 source endpoints at 12238. -/
namespace BstLean.Part264b.N12238
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12238 cell12238)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12238 (gMinus 12238) (1 - (cell12238 i).lower) ≤ 1 ∧
    energyUpper 12238 (gMinus 12238) (BstLean.Part211.gPlus 12238)
      (finiteEnergy 12238 12238 0.011) (1 - (cell12238 i).lower) ≤
      (cell12238 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12238) (by norm_num)
        (q := 1 - (cell12238 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12238,cell12238]) (by norm_num [scalarRow12238,cell12238])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12238,cell12238])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12238

/-! Source-cell containment and simple scalar guards at 12238. -/
namespace BstLean.Part264b.N12238
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12238 cell12238)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12238 ⟨10,by decide⟩).lower ∧ (cell12238 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12238 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12238 ⟨11,by decide⟩).lower ∧ (cell12238 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12238 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12238 ⟨12,by decide⟩).lower ∧ (cell12238 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12238 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12238 ⟨13,by decide⟩).lower ∧ (cell12238 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12238 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12238 ⟨14,by decide⟩).lower ∧ (cell12238 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12238 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12238 ⟨15,by decide⟩).lower ∧ (cell12238 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12238 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12238 ⟨16,by decide⟩).lower ∧ (cell12238 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12238 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12238 ⟨17,by decide⟩).lower ∧ (cell12238 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12238 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12238 ⟨18,by decide⟩).lower ∧ (cell12238 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12238 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12238 ⟨19,by decide⟩).lower ∧ (cell12238 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12238 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12238 ⟨20,by decide⟩).lower ∧ (cell12238 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12238 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12238 ⟨21,by decide⟩).lower ∧ (cell12238 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12238 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12238 ⟨22,by decide⟩).lower ∧ (cell12238 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12238 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12238 ⟨23,by decide⟩).lower ∧ (cell12238 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12238 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12238 ⟨24,by decide⟩).lower ∧ (cell12238 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12238 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12238 ⟨25,by decide⟩).lower ∧ (cell12238 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12238 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12238 ⟨26,by decide⟩).lower ∧ (cell12238 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12238 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12238 ⟨27,by decide⟩).lower ∧ (cell12238 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12238 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12238 ⟨28,by decide⟩).lower ∧ (cell12238 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12238 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12238 ⟨29,by decide⟩).lower ∧ (cell12238 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12238 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12238 ⟨30,by decide⟩).lower ∧ (cell12238 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12238 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12238 ⟨31,by decide⟩).lower ∧ (cell12238 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12238 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12238 ⟨32,by decide⟩).lower ∧ (cell12238 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12238 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12238 ⟨33,by decide⟩).lower ∧ (cell12238 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12238 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12238 ⟨34,by decide⟩).lower ∧ (cell12238 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12238 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12238 ⟨35,by decide⟩).lower ∧ (cell12238 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12238 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12238 ⟨36,by decide⟩).lower ∧ (cell12238 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12238 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12238 ⟨37,by decide⟩).lower ∧ (cell12238 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12238 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12238 ⟨38,by decide⟩).lower ∧ (cell12238 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12238 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12238 ⟨39,by decide⟩).lower ∧ (cell12238 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12238 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12238 ⟨40,by decide⟩).lower ∧ (cell12238 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12238 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12238 ⟨41,by decide⟩).lower ∧ (cell12238 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12238 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12238 ⟨42,by decide⟩).lower ∧ (cell12238 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12238 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12238 ⟨43,by decide⟩).lower ∧ (cell12238 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12238 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12238 ⟨44,by decide⟩).lower ∧ (cell12238 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12238 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12238 ⟨45,by decide⟩).lower ∧ (cell12238 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12238 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12238 ⟨46,by decide⟩).lower ∧ (cell12238 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12238 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12238 ⟨47,by decide⟩).lower ∧ (cell12238 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12238 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12238 ⟨48,by decide⟩).lower ∧ (cell12238 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12238 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12238 ⟨49,by decide⟩).lower ∧ (cell12238 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12238 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12238 ⟨50,by decide⟩).lower ∧ (cell12238 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12238 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12238 ⟨51,by decide⟩).lower ∧ (cell12238 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12238 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12238 ⟨52,by decide⟩).lower ∧ (cell12238 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12238 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12238 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12238 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12238,cell12238,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12238 i).lower ∧
    (cell12238 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12238 i).upper ≤ (0.532 : ℝ) ∧
    (cell12238 i).centre ≤ (0.1 : ℝ) ∧ (cell12238 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12238 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12238 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12238

/-! The local source numeric instances at 12238 have no network premises. -/
namespace BstLean.Part264b.N12238
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12238 cell12238)

noncomputable def sourceNumerics12238 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12238 (cell12238 i)
      scalarRow12238.M scalarRow12238.H scalarRow12238.xi := by
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
    energy_allowance := scalarRow12238.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12238]
    centre_nonneg := (scalarRow12238.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12238]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12238
/-! Actual 12239 scalar aliases and the unchanged imported parallel allowance. -/
