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
namespace BstLean.Part264b.N12263
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12263 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12263 12263 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12263.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12263 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12263 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12263 := gPlus_lower 12263
end BstLean.Part264b.N12263

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12263
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036447339328 : ℝ) ≤ wn 12263 := by
  have hn : √(12263 : ℝ) ≤ 110.738430546943 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12263 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.738430546943 ≤ 2 / √12263 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261017511 : ℝ) ≤ rhoBar 12263 BstLean.Part154.csC ∧
    rhoBar 12263 BstLean.Part154.csC ≤ 0.000261032436 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036447339328 : ℝ) / (1.295212 * 12263) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12263) := by gcongr
      _ ≤ (0.000261032436 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12263 BstLean.Part154.csC) ≤ 0.001044197882 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12263 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12263 BstLean.Part154.csC) (piBar (rhoBar 12263 BstLean.Part154.csC)) ≤ 0.000199378672 ∧
    cc1 (rhoBar 12263 BstLean.Part154.csC) (piBar (rhoBar 12263 BstLean.Part154.csC)) ≤ 0.000126865904 ∧
    cc2 (rhoBar 12263 BstLean.Part154.csC) ≤ 0.000073646545 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12263 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12263 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12263 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12263 BstLean.Part154.csC * nuR (rhoBar 12263 BstLean.Part154.csC)) ≤ 0.000522081907 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261032436 : ℝ) * 0.001044197882 := by gcongr
      _ ≤ (0.000522081907 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12263 BstLean.Part154.csC) * nuR (rhoBar 12263 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044197882 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12263 BstLean.Part154.csC) * rhoBar 12263 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261032436 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261032436 / 2 + 0.399 * 0.001044197882 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199378672 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522081907 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126865904 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261032436 / 1.414213562 := by gcongr
      _ ≤ (0.000073646545 : ℝ) := by norm_num

end BstLean.Part264b.N12263

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12263
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12263 BstLean.Part154.csC) (piBar (rhoBar 12263 BstLean.Part154.csC)) ≤ 1.71669E-7 := by
  have hr0 : 0 ≤ rhoBar 12263 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12263 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12263 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12263 BstLean.Part154.csC) (piBar (rhoBar 12263 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12263 BstLean.Part154.csC) (piBar (rhoBar 12263 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12263 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199378672 : ℝ) ^ 2 + 0.000126865904 ^ 2 + 3 * 0.000073646545 ^ 2 +
        2 * 0.797885 * 0.000199378672 * 0.000126865904 + 2 * 0.000199378672 * 0.000073646545 +
        4 * 0.797885 * 0.000126865904 * 0.000073646545 := by gcongr
    _ ≤ (1.71669E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12263 BstLean.Part154.csC Θ ≤ 0.002726802140 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12263 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12263 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12263 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12263 BstLean.Part154.csC) (piBar (rhoBar 12263 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12263 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71669E-7 / (0.000261017511 : ℝ) := by gcongr
    _ ≤ 0.002726802140 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12263 BstLean.Part154.csC Θ ≤ 0.003027398713 + 0.000688979155 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12263 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12263 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12263 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261032436 +
        (6863 / 10000) * 0.000261032436 * 12263 * 0.001044197882) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003027398713 + 0.000688979155 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12263 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12263 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12263 0.011 Θ ∧ gammaRatio 12263 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12263 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12263) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12263 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12263 0.011 Θ) :=
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
    badAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12263 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12263 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12263 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12263 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12263 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12263 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12263 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12263 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12263 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12263 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12263 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004127398713 + 0.003415781295 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12263

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12263
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12263 BstLean.Part154.csC) (piBar (rhoBar 12263 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12263 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12263 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12263 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12263 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12263 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12263 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12263 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12263 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12263 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12263 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12263 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12263 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053421512240 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12263) ≤ 0.010784310155 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12263 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010784310155 + 2 * 0.737676 / 12263) := by gcongr
    _ ≤ (0.053421512240 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12263 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12263

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12263
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483101606 : ℝ) ≤ plow 12263 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12263) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053427283893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431571124) : eMP 12263 0.011 xi bn ≤ 0.001231748688 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12263 : ℝ) * (1 - 0.011))) ≤ 0.000608954600 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001431571124 / (12263 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608954600 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608954600 : ℝ) + 3.141593 * 0.053427283893 / (12263 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001231748688 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053427283893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431571124) : PiBarMP 12263 12 0.011 xi bn ≤ 0.164132746795 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12263 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037836108733 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.127684984294 : ℝ) ≤ √((12263 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.738430546942 : ℝ) ≤ √12263 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12263) ≤ 0.125813669148 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037836108733 + 0.053427283893 * 1.772454 / (2 * (110.127684984294 : ℝ))) * (1 + 0.001231748688) +
        8 / (12263 * 110.738430546942) + 0.125813669148 := by gcongr
    _ ≤ (0.164132746795 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053427283893)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431571124) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284564939344) :
    parallelOracle 12263 0.011 xi bn cd ≤ 0.165161341626 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12263 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12263 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483101606 : ℝ) ≤ plow 12263 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.738430546942 : ℝ) ≤ √12263 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284564939344 : ℝ) / (2 * 0.560483101606 * 110.738430546942)) * 0.164132746795 +
        0.284564939344 ^ 2 / (2 * 0.560483101606 * 110.738430546942) := by gcongr
    _ ≤ (0.165161341626 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053427283893) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431571124)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284564939344) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12263 12263 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483101606 : ℝ) ≤ plow 12263 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.738430546942 : ℝ) ≤ √12263 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12263 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12263 Θ 1.22 ≤ 0.011975070384 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.738430546942 := by gcongr <;> linarith
      _ ≤ (0.011975070384 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12263 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12263 12263 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12263 12263 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12263 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12263 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12263 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12263 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165161341626 + 0.011975070384 + (0.008646 : ℝ) *
        (1 + 2 * (0.284564939344 + 0.011975070384) / (0.560483101606 * 110.738430546942))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12263]

end BstLean.Part264b.N12263

/-! The original eight local profiles supply actual 12263 moment certificates. -/
namespace BstLean.Part264b.N12263
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12263 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053427283893 ∧
    0 ≤ bN 12263 BstLean.Part154.csC (groupTheta g) ∧ bN 12263 BstLean.Part154.csC (groupTheta g) ≤ 0.001431571124 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12263 12263 0.011
      (momentAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12263 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12263 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12263 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231143427104 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12263 0.011
      (momentAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12263 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12263
/-! The actual computed-centre upper energy formula at 12263. -/
namespace BstLean.Part264b.N12263
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12263

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12263
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12263 cell12263)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086885878471
  | 2 => 0.087857226905
  | 3 => 0.088831343961
  | 4 => 0.089810675908
  | 5 => 0.090798141043
  | 6 => 0.091797194315
  | 7 => 0.092811897059
  | 8 => 0.093846991727
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12263 12263 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12263 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12263

/-! Actual upper energy certificates on all 43 source endpoints at 12263. -/
namespace BstLean.Part264b.N12263
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12263 cell12263)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12263 (gMinus 12263) (1 - (cell12263 i).lower) ≤ 1 ∧
    energyUpper 12263 (gMinus 12263) (BstLean.Part211.gPlus 12263)
      (finiteEnergy 12263 12263 0.011) (1 - (cell12263 i).lower) ≤
      (cell12263 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12263) (by norm_num)
        (q := 1 - (cell12263 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12263,cell12263]) (by norm_num [scalarRow12263,cell12263])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12263,cell12263])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12263

/-! Source-cell containment and simple scalar guards at 12263. -/
namespace BstLean.Part264b.N12263
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12263 cell12263)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12263 ⟨10,by decide⟩).lower ∧ (cell12263 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12263 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12263 ⟨11,by decide⟩).lower ∧ (cell12263 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12263 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12263 ⟨12,by decide⟩).lower ∧ (cell12263 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12263 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12263 ⟨13,by decide⟩).lower ∧ (cell12263 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12263 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12263 ⟨14,by decide⟩).lower ∧ (cell12263 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12263 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12263 ⟨15,by decide⟩).lower ∧ (cell12263 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12263 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12263 ⟨16,by decide⟩).lower ∧ (cell12263 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12263 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12263 ⟨17,by decide⟩).lower ∧ (cell12263 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12263 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12263 ⟨18,by decide⟩).lower ∧ (cell12263 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12263 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12263 ⟨19,by decide⟩).lower ∧ (cell12263 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12263 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12263 ⟨20,by decide⟩).lower ∧ (cell12263 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12263 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12263 ⟨21,by decide⟩).lower ∧ (cell12263 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12263 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12263 ⟨22,by decide⟩).lower ∧ (cell12263 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12263 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12263 ⟨23,by decide⟩).lower ∧ (cell12263 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12263 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12263 ⟨24,by decide⟩).lower ∧ (cell12263 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12263 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12263 ⟨25,by decide⟩).lower ∧ (cell12263 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12263 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12263 ⟨26,by decide⟩).lower ∧ (cell12263 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12263 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12263 ⟨27,by decide⟩).lower ∧ (cell12263 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12263 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12263 ⟨28,by decide⟩).lower ∧ (cell12263 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12263 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12263 ⟨29,by decide⟩).lower ∧ (cell12263 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12263 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12263 ⟨30,by decide⟩).lower ∧ (cell12263 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12263 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12263 ⟨31,by decide⟩).lower ∧ (cell12263 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12263 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12263 ⟨32,by decide⟩).lower ∧ (cell12263 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12263 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12263 ⟨33,by decide⟩).lower ∧ (cell12263 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12263 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12263 ⟨34,by decide⟩).lower ∧ (cell12263 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12263 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12263 ⟨35,by decide⟩).lower ∧ (cell12263 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12263 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12263 ⟨36,by decide⟩).lower ∧ (cell12263 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12263 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12263 ⟨37,by decide⟩).lower ∧ (cell12263 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12263 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12263 ⟨38,by decide⟩).lower ∧ (cell12263 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12263 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12263 ⟨39,by decide⟩).lower ∧ (cell12263 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12263 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12263 ⟨40,by decide⟩).lower ∧ (cell12263 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12263 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12263 ⟨41,by decide⟩).lower ∧ (cell12263 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12263 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12263 ⟨42,by decide⟩).lower ∧ (cell12263 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12263 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12263 ⟨43,by decide⟩).lower ∧ (cell12263 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12263 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12263 ⟨44,by decide⟩).lower ∧ (cell12263 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12263 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12263 ⟨45,by decide⟩).lower ∧ (cell12263 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12263 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12263 ⟨46,by decide⟩).lower ∧ (cell12263 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12263 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12263 ⟨47,by decide⟩).lower ∧ (cell12263 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12263 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12263 ⟨48,by decide⟩).lower ∧ (cell12263 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12263 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12263 ⟨49,by decide⟩).lower ∧ (cell12263 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12263 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12263 ⟨50,by decide⟩).lower ∧ (cell12263 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12263 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12263 ⟨51,by decide⟩).lower ∧ (cell12263 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12263 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12263 ⟨52,by decide⟩).lower ∧ (cell12263 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12263 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12263 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12263 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12263,cell12263,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12263 i).lower ∧
    (cell12263 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12263 i).upper ≤ (0.532 : ℝ) ∧
    (cell12263 i).centre ≤ (0.1 : ℝ) ∧ (cell12263 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12263 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12263 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12263

/-! The local source numeric instances at 12263 have no network premises. -/
namespace BstLean.Part264b.N12263
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12263 cell12263)

noncomputable def sourceNumerics12263 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12263 (cell12263 i)
      scalarRow12263.M scalarRow12263.H scalarRow12263.xi := by
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
    energy_allowance := scalarRow12263.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12263]
    centre_nonneg := (scalarRow12263.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12263]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12263
/-! Actual 12264 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12264
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12264 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12264 12264 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12264.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12264 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12264 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12264 := gPlus_lower 12264
end BstLean.Part264b.N12264

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12264
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036445840051 : ℝ) ≤ wn 12264 := by
  have hn : √(12264 : ℝ) ≤ 110.742945599258 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12264 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.742945599258 ≤ 2 / √12264 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260995850 : ℝ) ≤ rhoBar 12264 BstLean.Part154.csC ∧
    rhoBar 12264 BstLean.Part154.csC ≤ 0.000261011152 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036445840051 : ℝ) / (1.295212 * 12264) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12264) := by gcongr
      _ ≤ (0.000261011152 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12264 BstLean.Part154.csC) ≤ 0.001044112735 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12264 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12264 BstLean.Part154.csC) (piBar (rhoBar 12264 BstLean.Part154.csC)) ≤ 0.000199362415 ∧
    cc1 (rhoBar 12264 BstLean.Part154.csC) (piBar (rhoBar 12264 BstLean.Part154.csC)) ≤ 0.000126855559 ∧
    cc2 (rhoBar 12264 BstLean.Part154.csC) ≤ 0.000073640540 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12264 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12264 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12264 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12264 BstLean.Part154.csC * nuR (rhoBar 12264 BstLean.Part154.csC)) ≤ 0.000522039336 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261011152 : ℝ) * 0.001044112735 := by gcongr
      _ ≤ (0.000522039336 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12264 BstLean.Part154.csC) * nuR (rhoBar 12264 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044112735 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12264 BstLean.Part154.csC) * rhoBar 12264 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261011152 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261011152 / 2 + 0.399 * 0.001044112735 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199362415 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522039336 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126855559 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261011152 / 1.414213562 := by gcongr
      _ ≤ (0.000073640540 : ℝ) := by norm_num

end BstLean.Part264b.N12264

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12264
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12264 BstLean.Part154.csC) (piBar (rhoBar 12264 BstLean.Part154.csC)) ≤ 1.71641E-7 := by
  have hr0 : 0 ≤ rhoBar 12264 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12264 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12264 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12264 BstLean.Part154.csC) (piBar (rhoBar 12264 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12264 BstLean.Part154.csC) (piBar (rhoBar 12264 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12264 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199362415 : ℝ) ^ 2 + 0.000126855559 ^ 2 + 3 * 0.000073640540 ^ 2 +
        2 * 0.797885 * 0.000199362415 * 0.000126855559 + 2 * 0.000199362415 * 0.000073640540 +
        4 * 0.797885 * 0.000126855559 * 0.000073640540 := by gcongr
    _ ≤ (1.71641E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12264 BstLean.Part154.csC Θ ≤ 0.002726583656 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12264 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12264 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12264 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12264 BstLean.Part154.csC) (piBar (rhoBar 12264 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12264 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71641E-7 / (0.000260995850 : ℝ) := by gcongr
    _ ≤ 0.002726583656 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12264 BstLean.Part154.csC Θ ≤ 0.003027151855 + 0.000688922977 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12264 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12264 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12264 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261011152 +
        (6863 / 10000) * 0.000261011152 * 12264 * 0.001044112735) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003027151855 + 0.000688922977 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12264 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12264 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12264 0.011 Θ ∧ gammaRatio 12264 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12264 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12264) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12264 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12264 0.011 Θ) :=
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
    badAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12264 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12264 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12264 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12264 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12264 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12264 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12264 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12264 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12264 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12264 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12264 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004127151855 + 0.003415506633 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12264

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12264
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12264 BstLean.Part154.csC) (piBar (rhoBar 12264 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12264 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12264 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12264 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12264 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12264 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12264 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12264 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12264 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12264 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12264 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12264 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12264 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053419310188 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12264) ≤ 0.010783870473 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12264 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010783870473 + 2 * 0.737676 / 12264) := by gcongr
    _ ≤ (0.053419310188 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12264 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12264

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12264
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483150106 : ℝ) ≤ plow 12264 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12264) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426892838)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431456420) : eMP 12264 0.011 xi bn ≤ 0.001231649012 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12264 : ℝ) * (1 - 0.011))) ≤ 0.000608905377 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001431456420 / (12264 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608905377 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608905377 : ℝ) + 3.141593 * 0.053426892838 / (12264 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001231649012 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426892838)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431456420) : PiBarMP 12264 12 0.011 xi bn ≤ 0.164126074367 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12264 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037834592902 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.132175135152 : ℝ) ≤ √((12264 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.742945599257 : ℝ) ≤ √12264 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12264) ≤ 0.125808539654 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037834592902 + 0.053426892838 * 1.772454 / (2 * (110.132175135152 : ℝ))) * (1 + 0.001231649012) +
        8 / (12264 * 110.742945599257) + 0.125808539654 := by gcongr
    _ ≤ (0.164126074367 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426892838)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431456420) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284561891376) :
    parallelOracle 12264 0.011 xi bn cd ≤ 0.165154593874 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12264 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12264 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483150106 : ℝ) ≤ plow 12264 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.742945599257 : ℝ) ≤ √12264 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284561891376 : ℝ) / (2 * 0.560483150106 * 110.742945599257)) * 0.164126074367 +
        0.284561891376 ^ 2 / (2 * 0.560483150106 * 110.742945599257) := by gcongr
    _ ≤ (0.165154593874 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426892838) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431456420)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284561891376) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12264 12264 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483150106 : ℝ) ≤ plow 12264 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.742945599257 : ℝ) ≤ √12264 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12264 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12264 Θ 1.22 ≤ 0.011974582154 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.742945599257 := by gcongr <;> linarith
      _ ≤ (0.011974582154 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12264 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12264 12264 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12264 12264 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12264 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12264 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12264 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12264 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165154593874 + 0.011974582154 + (0.008646 : ℝ) *
        (1 + 2 * (0.284561891376 + 0.011974582154) / (0.560483150106 * 110.742945599257))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12264]

end BstLean.Part264b.N12264

/-! The original eight local profiles supply actual 12264 moment certificates. -/
namespace BstLean.Part264b.N12264
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12264 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053426892838 ∧
    0 ≤ bN 12264 BstLean.Part154.csC (groupTheta g) ∧ bN 12264 BstLean.Part154.csC (groupTheta g) ≤ 0.001431456420 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12264 12264 0.011
      (momentAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12264 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12264 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12264 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231142581188 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12264 0.011
      (momentAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12264 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12264
/-! The actual computed-centre upper energy formula at 12264. -/
namespace BstLean.Part264b.N12264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12264

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12264
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12264 cell12264)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086882361569
  | 2 => 0.087853630241
  | 3 => 0.088827653610
  | 4 => 0.089806874943
  | 5 => 0.090794209042
  | 6 => 0.091793106809
  | 7 => 0.092807624930
  | 8 => 0.093842500539
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12264 12264 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12264 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12264

/-! Actual upper energy certificates on all 43 source endpoints at 12264. -/
namespace BstLean.Part264b.N12264
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12264 cell12264)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12264 (gMinus 12264) (1 - (cell12264 i).lower) ≤ 1 ∧
    energyUpper 12264 (gMinus 12264) (BstLean.Part211.gPlus 12264)
      (finiteEnergy 12264 12264 0.011) (1 - (cell12264 i).lower) ≤
      (cell12264 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12264) (by norm_num)
        (q := 1 - (cell12264 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12264,cell12264]) (by norm_num [scalarRow12264,cell12264])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12264,cell12264])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12264

/-! Source-cell containment and simple scalar guards at 12264. -/
namespace BstLean.Part264b.N12264
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12264 cell12264)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12264 ⟨10,by decide⟩).lower ∧ (cell12264 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12264 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12264 ⟨11,by decide⟩).lower ∧ (cell12264 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12264 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12264 ⟨12,by decide⟩).lower ∧ (cell12264 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12264 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12264 ⟨13,by decide⟩).lower ∧ (cell12264 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12264 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12264 ⟨14,by decide⟩).lower ∧ (cell12264 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12264 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12264 ⟨15,by decide⟩).lower ∧ (cell12264 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12264 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12264 ⟨16,by decide⟩).lower ∧ (cell12264 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12264 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12264 ⟨17,by decide⟩).lower ∧ (cell12264 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12264 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12264 ⟨18,by decide⟩).lower ∧ (cell12264 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12264 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12264 ⟨19,by decide⟩).lower ∧ (cell12264 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12264 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12264 ⟨20,by decide⟩).lower ∧ (cell12264 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12264 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12264 ⟨21,by decide⟩).lower ∧ (cell12264 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12264 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12264 ⟨22,by decide⟩).lower ∧ (cell12264 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12264 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12264 ⟨23,by decide⟩).lower ∧ (cell12264 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12264 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12264 ⟨24,by decide⟩).lower ∧ (cell12264 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12264 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12264 ⟨25,by decide⟩).lower ∧ (cell12264 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12264 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12264 ⟨26,by decide⟩).lower ∧ (cell12264 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12264 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12264 ⟨27,by decide⟩).lower ∧ (cell12264 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12264 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12264 ⟨28,by decide⟩).lower ∧ (cell12264 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12264 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12264 ⟨29,by decide⟩).lower ∧ (cell12264 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12264 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12264 ⟨30,by decide⟩).lower ∧ (cell12264 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12264 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12264 ⟨31,by decide⟩).lower ∧ (cell12264 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12264 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12264 ⟨32,by decide⟩).lower ∧ (cell12264 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12264 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12264 ⟨33,by decide⟩).lower ∧ (cell12264 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12264 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12264 ⟨34,by decide⟩).lower ∧ (cell12264 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12264 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12264 ⟨35,by decide⟩).lower ∧ (cell12264 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12264 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12264 ⟨36,by decide⟩).lower ∧ (cell12264 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12264 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12264 ⟨37,by decide⟩).lower ∧ (cell12264 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12264 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12264 ⟨38,by decide⟩).lower ∧ (cell12264 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12264 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12264 ⟨39,by decide⟩).lower ∧ (cell12264 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12264 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12264 ⟨40,by decide⟩).lower ∧ (cell12264 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12264 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12264 ⟨41,by decide⟩).lower ∧ (cell12264 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12264 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12264 ⟨42,by decide⟩).lower ∧ (cell12264 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12264 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12264 ⟨43,by decide⟩).lower ∧ (cell12264 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12264 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12264 ⟨44,by decide⟩).lower ∧ (cell12264 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12264 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12264 ⟨45,by decide⟩).lower ∧ (cell12264 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12264 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12264 ⟨46,by decide⟩).lower ∧ (cell12264 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12264 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12264 ⟨47,by decide⟩).lower ∧ (cell12264 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12264 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12264 ⟨48,by decide⟩).lower ∧ (cell12264 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12264 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12264 ⟨49,by decide⟩).lower ∧ (cell12264 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12264 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12264 ⟨50,by decide⟩).lower ∧ (cell12264 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12264 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12264 ⟨51,by decide⟩).lower ∧ (cell12264 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12264 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12264 ⟨52,by decide⟩).lower ∧ (cell12264 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12264 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12264 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12264 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12264,cell12264,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12264 i).lower ∧
    (cell12264 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12264 i).upper ≤ (0.532 : ℝ) ∧
    (cell12264 i).centre ≤ (0.1 : ℝ) ∧ (cell12264 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12264 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12264 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12264

/-! The local source numeric instances at 12264 have no network premises. -/
namespace BstLean.Part264b.N12264
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12264 cell12264)

noncomputable def sourceNumerics12264 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12264 (cell12264 i)
      scalarRow12264.M scalarRow12264.H scalarRow12264.xi := by
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
    energy_allowance := scalarRow12264.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12264]
    centre_nonneg := (scalarRow12264.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12264]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12264
/-! Actual 12265 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12265
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12265 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12265 12265 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12265.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12265 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12265 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12265 := gPlus_lower 12265
end BstLean.Part264b.N12265

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12265
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036444340959 : ℝ) ≤ wn 12265 := by
  have hn : √(12265 : ℝ) ≤ 110.747460467498 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12265 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.747460467498 ≤ 2 / √12265 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260974193 : ℝ) ≤ rhoBar 12265 BstLean.Part154.csC ∧
    rhoBar 12265 BstLean.Part154.csC ≤ 0.000260989871 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036444340959 : ℝ) / (1.295212 * 12265) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12265) := by gcongr
      _ ≤ (0.000260989871 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12265 BstLean.Part154.csC) ≤ 0.001044027600 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12265 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12265 BstLean.Part154.csC) (piBar (rhoBar 12265 BstLean.Part154.csC)) ≤ 0.000199346159 ∧
    cc1 (rhoBar 12265 BstLean.Part154.csC) (piBar (rhoBar 12265 BstLean.Part154.csC)) ≤ 0.000126845216 ∧
    cc2 (rhoBar 12265 BstLean.Part154.csC) ≤ 0.000073634536 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12265 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12265 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12265 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12265 BstLean.Part154.csC * nuR (rhoBar 12265 BstLean.Part154.csC)) ≤ 0.000521996771 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260989871 : ℝ) * 0.001044027600 := by gcongr
      _ ≤ (0.000521996771 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12265 BstLean.Part154.csC) * nuR (rhoBar 12265 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044027600 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12265 BstLean.Part154.csC) * rhoBar 12265 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260989871 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260989871 / 2 + 0.399 * 0.001044027600 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199346159 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521996771 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126845216 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260989871 / 1.414213562 := by gcongr
      _ ≤ (0.000073634536 : ℝ) := by norm_num

end BstLean.Part264b.N12265

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12265
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12265 BstLean.Part154.csC) (piBar (rhoBar 12265 BstLean.Part154.csC)) ≤ 1.71613E-7 := by
  have hr0 : 0 ≤ rhoBar 12265 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12265 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12265 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12265 BstLean.Part154.csC) (piBar (rhoBar 12265 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12265 BstLean.Part154.csC) (piBar (rhoBar 12265 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12265 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199346159 : ℝ) ^ 2 + 0.000126845216 ^ 2 + 3 * 0.000073634536 ^ 2 +
        2 * 0.797885 * 0.000199346159 * 0.000126845216 + 2 * 0.000199346159 * 0.000073634536 +
        4 * 0.797885 * 0.000126845216 * 0.000073634536 := by gcongr
    _ ≤ (1.71613E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12265 BstLean.Part154.csC Θ ≤ 0.002726365095 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12265 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12265 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12265 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12265 BstLean.Part154.csC) (piBar (rhoBar 12265 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12265 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71613E-7 / (0.000260974193 : ℝ) := by gcongr
    _ ≤ 0.002726365095 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12265 BstLean.Part154.csC Θ ≤ 0.003026905026 + 0.000688866807 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12265 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12265 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12265 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260989871 +
        (6863 / 10000) * 0.000260989871 * 12265 * 0.001044027600) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003026905026 + 0.000688866807 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12265 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12265 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12265 0.011 Θ ∧ gammaRatio 12265 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12265 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12265) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12265 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12265 0.011 Θ) :=
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
    badAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12265 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12265 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12265 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12265 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12265 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12265 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12265 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12265 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12265 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12265 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12265 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004126905026 + 0.003415231902 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12265

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12265
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12265 BstLean.Part154.csC) (piBar (rhoBar 12265 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12265 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12265 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12265 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12265 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12265 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12265 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12265 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12265 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12265 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12265 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12265 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12265 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053417108404 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12265) ≤ 0.010783430844 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12265 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010783430844 + 2 * 0.737676 / 12265) := by gcongr
    _ ≤ (0.053417108404 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12265 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12265

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12265
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483198597 : ℝ) ≤ plow 12265 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12265) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426501775)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431341675) : eMP 12265 0.011 xi bn ≤ 0.001231549326 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12265 : ℝ) * (1 - 0.011))) ≤ 0.000608856149 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001431341675 / (12265 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608856149 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608856149 : ℝ) + 3.141593 * 0.053426501775 / (12265 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001231549326 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426501775)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431341675) : PiBarMP 12265 12 0.011 xi bn ≤ 0.164119401965 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12265 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037833076468 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.136665102952 : ℝ) ≤ √((12265 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.747460467497 : ℝ) ≤ √12265 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12265) ≤ 0.125803410787 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037833076468 + 0.053426501775 * 1.772454 / (2 * (110.136665102952 : ℝ))) * (1 + 0.001231549326) +
        8 / (12265 * 110.747460467497) + 0.125803410787 := by gcongr
    _ ≤ (0.164119401965 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426501775)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431341675) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284558843656) :
    parallelOracle 12265 0.011 xi bn cd ≤ 0.165147846158 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12265 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12265 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483198597 : ℝ) ≤ plow 12265 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.747460467497 : ℝ) ≤ √12265 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284558843656 : ℝ) / (2 * 0.560483198597 * 110.747460467497)) * 0.164119401965 +
        0.284558843656 ^ 2 / (2 * 0.560483198597 * 110.747460467497) := by gcongr
    _ ≤ (0.165147846158 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426501775) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431341675)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284558843656) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12265 12265 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483198597 : ℝ) ≤ plow 12265 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.747460467497 : ℝ) ≤ √12265 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12265 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12265 Θ 1.22 ≤ 0.011974093983 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.747460467497 := by gcongr <;> linarith
      _ ≤ (0.011974093983 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12265 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12265 12265 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12265 12265 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12265 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12265 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12265 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12265 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165147846158 + 0.011974093983 + (0.008646 : ℝ) *
        (1 + 2 * (0.284558843656 + 0.011974093983) / (0.560483198597 * 110.747460467497))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12265]

end BstLean.Part264b.N12265

/-! The original eight local profiles supply actual 12265 moment certificates. -/
namespace BstLean.Part264b.N12265
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12265 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053426501775 ∧
    0 ≤ bN 12265 BstLean.Part154.csC (groupTheta g) ∧ bN 12265 BstLean.Part154.csC (groupTheta g) ≤ 0.001431341675 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12265 12265 0.011
      (momentAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12265 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12265 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12265 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231141735252 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12265 0.011
      (momentAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12265 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12265
/-! The actual computed-centre upper energy formula at 12265. -/
namespace BstLean.Part264b.N12265
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12265

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12265
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12265 cell12265)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086878846394
  | 2 => 0.087850035383
  | 3 => 0.088823965163
  | 4 => 0.089803076001
  | 5 => 0.090790279208
  | 6 => 0.091789021645
  | 7 => 0.092803355351
  | 8 => 0.093838012153
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12265 12265 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12265 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12265

/-! Actual upper energy certificates on all 43 source endpoints at 12265. -/
namespace BstLean.Part264b.N12265
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12265 cell12265)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12265 (gMinus 12265) (1 - (cell12265 i).lower) ≤ 1 ∧
    energyUpper 12265 (gMinus 12265) (BstLean.Part211.gPlus 12265)
      (finiteEnergy 12265 12265 0.011) (1 - (cell12265 i).lower) ≤
      (cell12265 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12265) (by norm_num)
        (q := 1 - (cell12265 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12265,cell12265]) (by norm_num [scalarRow12265,cell12265])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12265,cell12265])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12265

/-! Source-cell containment and simple scalar guards at 12265. -/
namespace BstLean.Part264b.N12265
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12265 cell12265)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12265 ⟨10,by decide⟩).lower ∧ (cell12265 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12265 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12265 ⟨11,by decide⟩).lower ∧ (cell12265 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12265 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12265 ⟨12,by decide⟩).lower ∧ (cell12265 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12265 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12265 ⟨13,by decide⟩).lower ∧ (cell12265 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12265 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12265 ⟨14,by decide⟩).lower ∧ (cell12265 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12265 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12265 ⟨15,by decide⟩).lower ∧ (cell12265 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12265 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12265 ⟨16,by decide⟩).lower ∧ (cell12265 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12265 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12265 ⟨17,by decide⟩).lower ∧ (cell12265 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12265 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12265 ⟨18,by decide⟩).lower ∧ (cell12265 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12265 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12265 ⟨19,by decide⟩).lower ∧ (cell12265 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12265 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12265 ⟨20,by decide⟩).lower ∧ (cell12265 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12265 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12265 ⟨21,by decide⟩).lower ∧ (cell12265 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12265 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12265 ⟨22,by decide⟩).lower ∧ (cell12265 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12265 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12265 ⟨23,by decide⟩).lower ∧ (cell12265 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12265 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12265 ⟨24,by decide⟩).lower ∧ (cell12265 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12265 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12265 ⟨25,by decide⟩).lower ∧ (cell12265 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12265 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12265 ⟨26,by decide⟩).lower ∧ (cell12265 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12265 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12265 ⟨27,by decide⟩).lower ∧ (cell12265 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12265 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12265 ⟨28,by decide⟩).lower ∧ (cell12265 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12265 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12265 ⟨29,by decide⟩).lower ∧ (cell12265 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12265 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12265 ⟨30,by decide⟩).lower ∧ (cell12265 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12265 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12265 ⟨31,by decide⟩).lower ∧ (cell12265 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12265 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12265 ⟨32,by decide⟩).lower ∧ (cell12265 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12265 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12265 ⟨33,by decide⟩).lower ∧ (cell12265 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12265 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12265 ⟨34,by decide⟩).lower ∧ (cell12265 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12265 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12265 ⟨35,by decide⟩).lower ∧ (cell12265 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12265 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12265 ⟨36,by decide⟩).lower ∧ (cell12265 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12265 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12265 ⟨37,by decide⟩).lower ∧ (cell12265 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12265 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12265 ⟨38,by decide⟩).lower ∧ (cell12265 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12265 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12265 ⟨39,by decide⟩).lower ∧ (cell12265 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12265 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12265 ⟨40,by decide⟩).lower ∧ (cell12265 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12265 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12265 ⟨41,by decide⟩).lower ∧ (cell12265 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12265 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12265 ⟨42,by decide⟩).lower ∧ (cell12265 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12265 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12265 ⟨43,by decide⟩).lower ∧ (cell12265 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12265 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12265 ⟨44,by decide⟩).lower ∧ (cell12265 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12265 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12265 ⟨45,by decide⟩).lower ∧ (cell12265 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12265 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12265 ⟨46,by decide⟩).lower ∧ (cell12265 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12265 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12265 ⟨47,by decide⟩).lower ∧ (cell12265 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12265 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12265 ⟨48,by decide⟩).lower ∧ (cell12265 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12265 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12265 ⟨49,by decide⟩).lower ∧ (cell12265 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12265 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12265 ⟨50,by decide⟩).lower ∧ (cell12265 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12265 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12265 ⟨51,by decide⟩).lower ∧ (cell12265 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12265 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12265 ⟨52,by decide⟩).lower ∧ (cell12265 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12265 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12265 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12265 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12265,cell12265,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12265 i).lower ∧
    (cell12265 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12265 i).upper ≤ (0.532 : ℝ) ∧
    (cell12265 i).centre ≤ (0.1 : ℝ) ∧ (cell12265 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12265 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12265 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12265

/-! The local source numeric instances at 12265 have no network premises. -/
namespace BstLean.Part264b.N12265
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12265 cell12265)

noncomputable def sourceNumerics12265 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12265 (cell12265 i)
      scalarRow12265.M scalarRow12265.H scalarRow12265.xi := by
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
    energy_allowance := scalarRow12265.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12265]
    centre_nonneg := (scalarRow12265.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12265]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12265
/-! Actual 12266 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12266
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12266 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12266 12266 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12266.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12266 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12266 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12266 := gPlus_lower 12266
end BstLean.Part264b.N12266

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12266
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036442842051 : ℝ) ≤ wn 12266 := by
  have hn : √(12266 : ℝ) ≤ 110.751975151688 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12266 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.751975151688 ≤ 2 / √12266 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260952539 : ℝ) ≤ rhoBar 12266 BstLean.Part154.csC ∧
    rhoBar 12266 BstLean.Part154.csC ≤ 0.000260968593 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036442842051 : ℝ) / (1.295212 * 12266) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12266) := by gcongr
      _ ≤ (0.000260968593 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12266 BstLean.Part154.csC) ≤ 0.001043942477 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12266 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12266 BstLean.Part154.csC) (piBar (rhoBar 12266 BstLean.Part154.csC)) ≤ 0.000199329906 ∧
    cc1 (rhoBar 12266 BstLean.Part154.csC) (piBar (rhoBar 12266 BstLean.Part154.csC)) ≤ 0.000126834874 ∧
    cc2 (rhoBar 12266 BstLean.Part154.csC) ≤ 0.000073628533 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12266 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12266 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12266 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12266 BstLean.Part154.csC * nuR (rhoBar 12266 BstLean.Part154.csC)) ≤ 0.000521954212 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260968593 : ℝ) * 0.001043942477 := by gcongr
      _ ≤ (0.000521954212 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12266 BstLean.Part154.csC) * nuR (rhoBar 12266 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043942477 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12266 BstLean.Part154.csC) * rhoBar 12266 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260968593 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260968593 / 2 + 0.399 * 0.001043942477 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199329906 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521954212 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126834874 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260968593 / 1.414213562 := by gcongr
      _ ≤ (0.000073628533 : ℝ) := by norm_num

end BstLean.Part264b.N12266

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12266
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12266 BstLean.Part154.csC) (piBar (rhoBar 12266 BstLean.Part154.csC)) ≤ 1.71585E-7 := by
  have hr0 : 0 ≤ rhoBar 12266 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12266 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12266 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12266 BstLean.Part154.csC) (piBar (rhoBar 12266 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12266 BstLean.Part154.csC) (piBar (rhoBar 12266 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12266 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199329906 : ℝ) ^ 2 + 0.000126834874 ^ 2 + 3 * 0.000073628533 ^ 2 +
        2 * 0.797885 * 0.000199329906 * 0.000126834874 + 2 * 0.000199329906 * 0.000073628533 +
        4 * 0.797885 * 0.000126834874 * 0.000073628533 := by gcongr
    _ ≤ (1.71585E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12266 BstLean.Part154.csC Θ ≤ 0.002726146465 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12266 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12266 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12266 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12266 BstLean.Part154.csC) (piBar (rhoBar 12266 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12266 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71585E-7 / (0.000260952539 : ℝ) := by gcongr
    _ ≤ 0.002726146465 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12266 BstLean.Part154.csC Θ ≤ 0.003026658227 + 0.000688810646 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12266 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12266 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12266 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260968593 +
        (6863 / 10000) * 0.000260968593 * 12266 * 0.001043942477) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003026658227 + 0.000688810646 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12266 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12266 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12266 0.011 Θ ∧ gammaRatio 12266 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12266 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12266) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12266 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12266 0.011 Θ) :=
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
    badAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12266 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12266 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12266 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12266 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12266 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12266 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12266 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12266 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12266 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12266 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12266 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004126658227 + 0.003414957111 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12266

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12266
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12266 BstLean.Part154.csC) (piBar (rhoBar 12266 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12266 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12266 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12266 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12266 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12266 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12266 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12266 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12266 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12266 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12266 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12266 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12266 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053414906891 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12266) ≤ 0.010782991269 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12266 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010782991269 + 2 * 0.737676 / 12266) := by gcongr
    _ ≤ (0.053414906891 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12266 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12266

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12266
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483247081 : ℝ) ≤ plow 12266 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12266) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426110711)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431226895) : eMP 12266 0.011 xi bn ≤ 0.001231449635 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12266 : ℝ) * (1 - 0.011))) ≤ 0.000608806918 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001431226895 / (12266 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608806918 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608806918 : ℝ) + 3.141593 * 0.053426110711 / (12266 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001231449635 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426110711)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431226895) : PiBarMP 12266 12 0.011 xi bn ≤ 0.164112729669 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12266 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037831559511 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.141154887716 : ℝ) ≤ √((12266 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.751975151687 : ℝ) ≤ √12266 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12266) ≤ 0.125798282547 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037831559511 + 0.053426110711 * 1.772454 / (2 * (110.141154887716 : ℝ))) * (1 + 0.001231449635) +
        8 / (12266 * 110.751975151687) + 0.125798282547 := by gcongr
    _ ≤ (0.164112729669 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426110711)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431226895) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284555796201) :
    parallelOracle 12266 0.011 xi bn cd ≤ 0.165141098558 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12266 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12266 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483247081 : ℝ) ≤ plow 12266 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.751975151687 : ℝ) ≤ √12266 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284555796201 : ℝ) / (2 * 0.560483247081 * 110.751975151687)) * 0.164112729669 +
        0.284555796201 ^ 2 / (2 * 0.560483247081 * 110.751975151687) := by gcongr
    _ ≤ (0.165141098558 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053426110711) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431226895)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284555796201) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12266 12266 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483247081 : ℝ) ≤ plow 12266 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.751975151687 : ℝ) ≤ √12266 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12266 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12266 Θ 1.22 ≤ 0.011973605872 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.751975151687 := by gcongr <;> linarith
      _ ≤ (0.011973605872 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12266 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12266 12266 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12266 12266 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12266 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12266 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12266 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12266 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165141098558 + 0.011973605872 + (0.008646 : ℝ) *
        (1 + 2 * (0.284555796201 + 0.011973605872) / (0.560483247081 * 110.751975151687))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12266]

end BstLean.Part264b.N12266

/-! The original eight local profiles supply actual 12266 moment certificates. -/
namespace BstLean.Part264b.N12266
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12266 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053426110711 ∧
    0 ≤ bN 12266 BstLean.Part154.csC (groupTheta g) ∧ bN 12266 BstLean.Part154.csC (groupTheta g) ≤ 0.001431226895 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12266 12266 0.011
      (momentAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12266 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12266 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12266 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231140889310 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12266 0.011
      (momentAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12266 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12266
/-! The actual computed-centre upper energy formula at 12266. -/
namespace BstLean.Part264b.N12266
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12266

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12266
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12266 cell12266)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086875332946
  | 2 => 0.087846442330
  | 3 => 0.088820278617
  | 4 => 0.089799279079
  | 5 => 0.090786351538
  | 6 => 0.091784938820
  | 7 => 0.092799088321
  | 8 => 0.093833526565
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12266 12266 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12266 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12266

/-! Actual upper energy certificates on all 43 source endpoints at 12266. -/
namespace BstLean.Part264b.N12266
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12266 cell12266)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12266 (gMinus 12266) (1 - (cell12266 i).lower) ≤ 1 ∧
    energyUpper 12266 (gMinus 12266) (BstLean.Part211.gPlus 12266)
      (finiteEnergy 12266 12266 0.011) (1 - (cell12266 i).lower) ≤
      (cell12266 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12266) (by norm_num)
        (q := 1 - (cell12266 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12266,cell12266]) (by norm_num [scalarRow12266,cell12266])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12266,cell12266])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12266

/-! Source-cell containment and simple scalar guards at 12266. -/
namespace BstLean.Part264b.N12266
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12266 cell12266)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12266 ⟨10,by decide⟩).lower ∧ (cell12266 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12266 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12266 ⟨11,by decide⟩).lower ∧ (cell12266 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12266 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12266 ⟨12,by decide⟩).lower ∧ (cell12266 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12266 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12266 ⟨13,by decide⟩).lower ∧ (cell12266 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12266 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12266 ⟨14,by decide⟩).lower ∧ (cell12266 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12266 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12266 ⟨15,by decide⟩).lower ∧ (cell12266 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12266 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12266 ⟨16,by decide⟩).lower ∧ (cell12266 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12266 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12266 ⟨17,by decide⟩).lower ∧ (cell12266 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12266 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12266 ⟨18,by decide⟩).lower ∧ (cell12266 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12266 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12266 ⟨19,by decide⟩).lower ∧ (cell12266 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12266 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12266 ⟨20,by decide⟩).lower ∧ (cell12266 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12266 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12266 ⟨21,by decide⟩).lower ∧ (cell12266 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12266 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12266 ⟨22,by decide⟩).lower ∧ (cell12266 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12266 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12266 ⟨23,by decide⟩).lower ∧ (cell12266 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12266 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12266 ⟨24,by decide⟩).lower ∧ (cell12266 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12266 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12266 ⟨25,by decide⟩).lower ∧ (cell12266 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12266 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12266 ⟨26,by decide⟩).lower ∧ (cell12266 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12266 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12266 ⟨27,by decide⟩).lower ∧ (cell12266 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12266 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12266 ⟨28,by decide⟩).lower ∧ (cell12266 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12266 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12266 ⟨29,by decide⟩).lower ∧ (cell12266 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12266 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12266 ⟨30,by decide⟩).lower ∧ (cell12266 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12266 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12266 ⟨31,by decide⟩).lower ∧ (cell12266 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12266 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12266 ⟨32,by decide⟩).lower ∧ (cell12266 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12266 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12266 ⟨33,by decide⟩).lower ∧ (cell12266 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12266 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12266 ⟨34,by decide⟩).lower ∧ (cell12266 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12266 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12266 ⟨35,by decide⟩).lower ∧ (cell12266 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12266 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12266 ⟨36,by decide⟩).lower ∧ (cell12266 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12266 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12266 ⟨37,by decide⟩).lower ∧ (cell12266 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12266 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12266 ⟨38,by decide⟩).lower ∧ (cell12266 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12266 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12266 ⟨39,by decide⟩).lower ∧ (cell12266 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12266 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12266 ⟨40,by decide⟩).lower ∧ (cell12266 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12266 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12266 ⟨41,by decide⟩).lower ∧ (cell12266 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12266 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12266 ⟨42,by decide⟩).lower ∧ (cell12266 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12266 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12266 ⟨43,by decide⟩).lower ∧ (cell12266 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12266 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12266 ⟨44,by decide⟩).lower ∧ (cell12266 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12266 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12266 ⟨45,by decide⟩).lower ∧ (cell12266 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12266 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12266 ⟨46,by decide⟩).lower ∧ (cell12266 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12266 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12266 ⟨47,by decide⟩).lower ∧ (cell12266 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12266 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12266 ⟨48,by decide⟩).lower ∧ (cell12266 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12266 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12266 ⟨49,by decide⟩).lower ∧ (cell12266 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12266 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12266 ⟨50,by decide⟩).lower ∧ (cell12266 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12266 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12266 ⟨51,by decide⟩).lower ∧ (cell12266 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12266 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12266 ⟨52,by decide⟩).lower ∧ (cell12266 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12266 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12266 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12266 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12266,cell12266,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12266 i).lower ∧
    (cell12266 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12266 i).upper ≤ (0.532 : ℝ) ∧
    (cell12266 i).centre ≤ (0.1 : ℝ) ∧ (cell12266 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12266 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12266 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12266

/-! The local source numeric instances at 12266 have no network premises. -/
namespace BstLean.Part264b.N12266
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12266 cell12266)

noncomputable def sourceNumerics12266 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12266 (cell12266 i)
      scalarRow12266.M scalarRow12266.H scalarRow12266.xi := by
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
    energy_allowance := scalarRow12266.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12266]
    centre_nonneg := (scalarRow12266.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12266]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12266
/-! Actual 12267 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12267
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12267 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12267 12267 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12267.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12267 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12267 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12267 := gPlus_lower 12267
end BstLean.Part264b.N12267

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12267
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036441343328 : ℝ) ≤ wn 12267 := by
  have hn : √(12267 : ℝ) ≤ 110.756489651849 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12267 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.756489651849 ≤ 2 / √12267 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260930889 : ℝ) ≤ rhoBar 12267 BstLean.Part154.csC ∧
    rhoBar 12267 BstLean.Part154.csC ≤ 0.000260947319 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036441343328 : ℝ) / (1.295212 * 12267) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12267) := by gcongr
      _ ≤ (0.000260947319 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12267 BstLean.Part154.csC) ≤ 0.001043857370 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12267 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12267 BstLean.Part154.csC) (piBar (rhoBar 12267 BstLean.Part154.csC)) ≤ 0.000199313656 ∧
    cc1 (rhoBar 12267 BstLean.Part154.csC) (piBar (rhoBar 12267 BstLean.Part154.csC)) ≤ 0.000126824534 ∧
    cc2 (rhoBar 12267 BstLean.Part154.csC) ≤ 0.000073622530 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12267 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12267 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12267 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12267 BstLean.Part154.csC * nuR (rhoBar 12267 BstLean.Part154.csC)) ≤ 0.000521911662 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260947319 : ℝ) * 0.001043857370 := by gcongr
      _ ≤ (0.000521911662 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12267 BstLean.Part154.csC) * nuR (rhoBar 12267 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043857370 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12267 BstLean.Part154.csC) * rhoBar 12267 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260947319 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260947319 / 2 + 0.399 * 0.001043857370 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199313656 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521911662 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126824534 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260947319 / 1.414213562 := by gcongr
      _ ≤ (0.000073622530 : ℝ) := by norm_num

end BstLean.Part264b.N12267

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12267
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12267 BstLean.Part154.csC) (piBar (rhoBar 12267 BstLean.Part154.csC)) ≤ 1.71557E-7 := by
  have hr0 : 0 ≤ rhoBar 12267 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12267 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12267 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12267 BstLean.Part154.csC) (piBar (rhoBar 12267 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12267 BstLean.Part154.csC) (piBar (rhoBar 12267 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12267 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199313656 : ℝ) ^ 2 + 0.000126824534 ^ 2 + 3 * 0.000073622530 ^ 2 +
        2 * 0.797885 * 0.000199313656 * 0.000126824534 + 2 * 0.000199313656 * 0.000073622530 +
        4 * 0.797885 * 0.000126824534 * 0.000073622530 := by gcongr
    _ ≤ (1.71557E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12267 BstLean.Part154.csC Θ ≤ 0.002725927758 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12267 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12267 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12267 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12267 BstLean.Part154.csC) (piBar (rhoBar 12267 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12267 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71557E-7 / (0.000260930889 : ℝ) := by gcongr
    _ ≤ 0.002725927758 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12267 BstLean.Part154.csC Θ ≤ 0.003026411480 + 0.000688754494 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12267 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12267 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12267 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260947319 +
        (6863 / 10000) * 0.000260947319 * 12267 * 0.001043857370) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003026411480 + 0.000688754494 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12267 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12267 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12267 0.011 Θ ∧ gammaRatio 12267 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12267 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12267) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12267 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12267 0.011 Θ) :=
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
    badAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12267 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12267 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12267 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12267 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12267 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12267 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12267 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12267 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12267 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12267 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12267 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004126411480 + 0.003414682252 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12267

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12267
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12267 BstLean.Part154.csC) (piBar (rhoBar 12267 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12267 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12267 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12267 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12267 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12267 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12267 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12267 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12267 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12267 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12267 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12267 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12267 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053412705652 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12267) ≤ 0.010782551748 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12267 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010782551748 + 2 * 0.737676 / 12267) := by gcongr
    _ ≤ (0.053412705652 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12267 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12267

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12267
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483295557 : ℝ) ≤ plow 12267 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12267) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053425719663)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431112073) : eMP 12267 0.011 xi bn ≤ 0.001231349934 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12267 : ℝ) * (1 - 0.011))) ≤ 0.000608757682 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001431112073 / (12267 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608757682 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608757682 : ℝ) + 3.141593 * 0.053425719663 / (12267 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001231349934 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053425719663)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431112073) : PiBarMP 12267 12 0.011 xi bn ≤ 0.164106057386 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12267 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037830041938 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.145644489466 : ℝ) ≤ √((12267 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.756489651848 : ℝ) ≤ √12267 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12267) ≤ 0.125793154935 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037830041938 + 0.053425719663 * 1.772454 / (2 * (110.145644489466 : ℝ))) * (1 + 0.001231349934) +
        8 / (12267 * 110.756489651848) + 0.125793154935 := by gcongr
    _ ≤ (0.164106057386 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053425719663)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431112073) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284552749053) :
    parallelOracle 12267 0.011 xi bn cd ≤ 0.165134350981 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12267 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12267 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483295557 : ℝ) ≤ plow 12267 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.756489651848 : ℝ) ≤ √12267 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284552749053 : ℝ) / (2 * 0.560483295557 * 110.756489651848)) * 0.164106057386 +
        0.284552749053 ^ 2 / (2 * 0.560483295557 * 110.756489651848) := by gcongr
    _ ≤ (0.165134350981 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053425719663) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431112073)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284552749053) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12267 12267 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483295557 : ℝ) ≤ plow 12267 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.756489651848 : ℝ) ≤ √12267 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12267 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12267 Θ 1.22 ≤ 0.011973117821 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.756489651848 := by gcongr <;> linarith
      _ ≤ (0.011973117821 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12267 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12267 12267 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12267 12267 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12267 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12267 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12267 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12267 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165134350981 + 0.011973117821 + (0.008646 : ℝ) *
        (1 + 2 * (0.284552749053 + 0.011973117821) / (0.560483295557 * 110.756489651848))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12267]

end BstLean.Part264b.N12267

/-! The original eight local profiles supply actual 12267 moment certificates. -/
namespace BstLean.Part264b.N12267
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12267 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053425719663 ∧
    0 ≤ bN 12267 BstLean.Part154.csC (groupTheta g) ∧ bN 12267 BstLean.Part154.csC (groupTheta g) ≤ 0.001431112073 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12267 12267 0.011
      (momentAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12267 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12267 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12267 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231140043401 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12267 0.011
      (momentAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12267 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12267
/-! The actual computed-centre upper energy formula at 12267. -/
namespace BstLean.Part264b.N12267
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12267

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12267
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12267 cell12267)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086871821221
  | 2 => 0.087842851079
  | 3 => 0.088816593970
  | 4 => 0.089795484175
  | 5 => 0.090782426030
  | 6 => 0.091780858330
  | 7 => 0.092794823835
  | 8 => 0.093829043773
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12267 12267 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12267 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12267

/-! Actual upper energy certificates on all 43 source endpoints at 12267. -/
namespace BstLean.Part264b.N12267
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12267 cell12267)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12267 (gMinus 12267) (1 - (cell12267 i).lower) ≤ 1 ∧
    energyUpper 12267 (gMinus 12267) (BstLean.Part211.gPlus 12267)
      (finiteEnergy 12267 12267 0.011) (1 - (cell12267 i).lower) ≤
      (cell12267 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12267) (by norm_num)
        (q := 1 - (cell12267 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12267,cell12267]) (by norm_num [scalarRow12267,cell12267])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12267,cell12267])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12267

/-! Source-cell containment and simple scalar guards at 12267. -/
namespace BstLean.Part264b.N12267
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12267 cell12267)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12267 ⟨10,by decide⟩).lower ∧ (cell12267 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12267 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12267 ⟨11,by decide⟩).lower ∧ (cell12267 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12267 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12267 ⟨12,by decide⟩).lower ∧ (cell12267 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12267 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12267 ⟨13,by decide⟩).lower ∧ (cell12267 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12267 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12267 ⟨14,by decide⟩).lower ∧ (cell12267 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12267 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12267 ⟨15,by decide⟩).lower ∧ (cell12267 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12267 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12267 ⟨16,by decide⟩).lower ∧ (cell12267 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12267 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12267 ⟨17,by decide⟩).lower ∧ (cell12267 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12267 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12267 ⟨18,by decide⟩).lower ∧ (cell12267 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12267 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12267 ⟨19,by decide⟩).lower ∧ (cell12267 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12267 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12267 ⟨20,by decide⟩).lower ∧ (cell12267 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12267 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12267 ⟨21,by decide⟩).lower ∧ (cell12267 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12267 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12267 ⟨22,by decide⟩).lower ∧ (cell12267 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12267 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12267 ⟨23,by decide⟩).lower ∧ (cell12267 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12267 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12267 ⟨24,by decide⟩).lower ∧ (cell12267 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12267 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12267 ⟨25,by decide⟩).lower ∧ (cell12267 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12267 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12267 ⟨26,by decide⟩).lower ∧ (cell12267 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12267 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12267 ⟨27,by decide⟩).lower ∧ (cell12267 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12267 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12267 ⟨28,by decide⟩).lower ∧ (cell12267 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12267 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12267 ⟨29,by decide⟩).lower ∧ (cell12267 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12267 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12267 ⟨30,by decide⟩).lower ∧ (cell12267 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12267 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12267 ⟨31,by decide⟩).lower ∧ (cell12267 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12267 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12267 ⟨32,by decide⟩).lower ∧ (cell12267 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12267 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12267 ⟨33,by decide⟩).lower ∧ (cell12267 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12267 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12267 ⟨34,by decide⟩).lower ∧ (cell12267 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12267 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12267 ⟨35,by decide⟩).lower ∧ (cell12267 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12267 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12267 ⟨36,by decide⟩).lower ∧ (cell12267 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12267 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12267 ⟨37,by decide⟩).lower ∧ (cell12267 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12267 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12267 ⟨38,by decide⟩).lower ∧ (cell12267 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12267 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12267 ⟨39,by decide⟩).lower ∧ (cell12267 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12267 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12267 ⟨40,by decide⟩).lower ∧ (cell12267 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12267 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12267 ⟨41,by decide⟩).lower ∧ (cell12267 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12267 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12267 ⟨42,by decide⟩).lower ∧ (cell12267 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12267 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12267 ⟨43,by decide⟩).lower ∧ (cell12267 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12267 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12267 ⟨44,by decide⟩).lower ∧ (cell12267 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12267 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12267 ⟨45,by decide⟩).lower ∧ (cell12267 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12267 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12267 ⟨46,by decide⟩).lower ∧ (cell12267 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12267 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12267 ⟨47,by decide⟩).lower ∧ (cell12267 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12267 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12267 ⟨48,by decide⟩).lower ∧ (cell12267 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12267 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12267 ⟨49,by decide⟩).lower ∧ (cell12267 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12267 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12267 ⟨50,by decide⟩).lower ∧ (cell12267 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12267 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12267 ⟨51,by decide⟩).lower ∧ (cell12267 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12267 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12267 ⟨52,by decide⟩).lower ∧ (cell12267 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12267 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12267 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12267 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12267,cell12267,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12267 i).lower ∧
    (cell12267 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12267 i).upper ≤ (0.532 : ℝ) ∧
    (cell12267 i).centre ≤ (0.1 : ℝ) ∧ (cell12267 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12267 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12267 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12267

/-! The local source numeric instances at 12267 have no network premises. -/
namespace BstLean.Part264b.N12267
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12267 cell12267)

noncomputable def sourceNumerics12267 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12267 (cell12267 i)
      scalarRow12267.M scalarRow12267.H scalarRow12267.xi := by
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
    energy_allowance := scalarRow12267.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12267]
    centre_nonneg := (scalarRow12267.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12267]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12267
/-! Actual 12268 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12268
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12268 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12268 12268 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12268.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12268 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12268 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12268 := gPlus_lower 12268
end BstLean.Part264b.N12268

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12268
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036439844789 : ℝ) ≤ wn 12268 := by
  have hn : √(12268 : ℝ) ≤ 110.761003968004 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12268 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.761003968004 ≤ 2 / √12268 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260909243 : ℝ) ≤ rhoBar 12268 BstLean.Part154.csC ∧
    rhoBar 12268 BstLean.Part154.csC ≤ 0.000260926049 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036439844789 : ℝ) / (1.295212 * 12268) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12268) := by gcongr
      _ ≤ (0.000260926049 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12268 BstLean.Part154.csC) ≤ 0.001043772279 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12268 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12268 BstLean.Part154.csC) (piBar (rhoBar 12268 BstLean.Part154.csC)) ≤ 0.000199297409 ∧
    cc1 (rhoBar 12268 BstLean.Part154.csC) (piBar (rhoBar 12268 BstLean.Part154.csC)) ≤ 0.000126814196 ∧
    cc2 (rhoBar 12268 BstLean.Part154.csC) ≤ 0.000073616529 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12268 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12268 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12268 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12268 BstLean.Part154.csC * nuR (rhoBar 12268 BstLean.Part154.csC)) ≤ 0.000521869119 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260926049 : ℝ) * 0.001043772279 := by gcongr
      _ ≤ (0.000521869119 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12268 BstLean.Part154.csC) * nuR (rhoBar 12268 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043772279 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12268 BstLean.Part154.csC) * rhoBar 12268 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260926049 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260926049 / 2 + 0.399 * 0.001043772279 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199297409 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521869119 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126814196 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260926049 / 1.414213562 := by gcongr
      _ ≤ (0.000073616529 : ℝ) := by norm_num

end BstLean.Part264b.N12268

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12268
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12268 BstLean.Part154.csC) (piBar (rhoBar 12268 BstLean.Part154.csC)) ≤ 1.71529E-7 := by
  have hr0 : 0 ≤ rhoBar 12268 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12268 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12268 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12268 BstLean.Part154.csC) (piBar (rhoBar 12268 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12268 BstLean.Part154.csC) (piBar (rhoBar 12268 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12268 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199297409 : ℝ) ^ 2 + 0.000126814196 ^ 2 + 3 * 0.000073616529 ^ 2 +
        2 * 0.797885 * 0.000199297409 * 0.000126814196 + 2 * 0.000199297409 * 0.000073616529 +
        4 * 0.797885 * 0.000126814196 * 0.000073616529 := by gcongr
    _ ≤ (1.71529E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12268 BstLean.Part154.csC Θ ≤ 0.002725708973 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12268 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12268 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12268 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12268 BstLean.Part154.csC) (piBar (rhoBar 12268 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12268 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71529E-7 / (0.000260909243 : ℝ) := by gcongr
    _ ≤ 0.002725708973 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12268 BstLean.Part154.csC Θ ≤ 0.003026164786 + 0.000688698353 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12268 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12268 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12268 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260926049 +
        (6863 / 10000) * 0.000260926049 * 12268 * 0.001043772279) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003026164786 + 0.000688698353 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12268 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12268 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12268 0.011 Θ ∧ gammaRatio 12268 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12268 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12268) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12268 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12268 0.011 Θ) :=
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
    badAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12268 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12268 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12268 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12268 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12268 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12268 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12268 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12268 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12268 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12268 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12268 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004126164786 + 0.003414407326 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12268

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12268
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12268 BstLean.Part154.csC) (piBar (rhoBar 12268 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12268 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12268 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12268 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12268 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12268 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12268 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12268 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12268 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12268 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12268 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12268 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12268 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053410504684 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12268) ≤ 0.010782112281 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12268 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010782112281 + 2 * 0.737676 / 12268) := by gcongr
    _ ≤ (0.053410504684 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12268 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12268

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12268
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483344025 : ℝ) ≤ plow 12268 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12268) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053425328633)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430997211) : eMP 12268 0.011 xi bn ≤ 0.001231250225 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12268 : ℝ) * (1 - 0.011))) ≤ 0.000608708442 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001430997211 / (12268 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608708442 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608708442 : ℝ) + 3.141593 * 0.053425328633 / (12268 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001231250225 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053425328633)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430997211) : PiBarMP 12268 12 0.011 xi bn ≤ 0.164099385143 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12268 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037828523776 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.150133908225 : ℝ) ≤ √((12268 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.761003968003 : ℝ) ≤ √12268 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12268) ≤ 0.125788027949 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037828523776 + 0.053425328633 * 1.772454 / (2 * (110.150133908225 : ℝ))) * (1 + 0.001231250225) +
        8 / (12268 * 110.761003968003) + 0.125788027949 := by gcongr
    _ ≤ (0.164099385143 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053425328633)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430997211) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284549702211) :
    parallelOracle 12268 0.011 xi bn cd ≤ 0.165127603454 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12268 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12268 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483344025 : ℝ) ≤ plow 12268 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.761003968003 : ℝ) ≤ √12268 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284549702211 : ℝ) / (2 * 0.560483344025 * 110.761003968003)) * 0.164099385143 +
        0.284549702211 ^ 2 / (2 * 0.560483344025 * 110.761003968003) := by gcongr
    _ ≤ (0.165127603454 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053425328633) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430997211)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284549702211) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12268 12268 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483344025 : ℝ) ≤ plow 12268 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.761003968003 : ℝ) ≤ √12268 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12268 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12268 Θ 1.22 ≤ 0.011972629830 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.761003968003 := by gcongr <;> linarith
      _ ≤ (0.011972629830 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12268 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12268 12268 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12268 12268 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12268 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12268 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12268 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12268 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165127603454 + 0.011972629830 + (0.008646 : ℝ) *
        (1 + 2 * (0.284549702211 + 0.011972629830) / (0.560483344025 * 110.761003968003))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12268]

end BstLean.Part264b.N12268

/-! The original eight local profiles supply actual 12268 moment certificates. -/
namespace BstLean.Part264b.N12268
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12268 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053425328633 ∧
    0 ≤ bN 12268 BstLean.Part154.csC (groupTheta g) ∧ bN 12268 BstLean.Part154.csC (groupTheta g) ≤ 0.001430997211 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12268 12268 0.011
      (momentAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12268 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12268 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12268 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231139197527 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12268 0.011
      (momentAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12268 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12268
/-! The actual computed-centre upper energy formula at 12268. -/
namespace BstLean.Part264b.N12268
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12268

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12268
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12268 cell12268)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086868311219
  | 2 => 0.087839261629
  | 3 => 0.088812911220
  | 4 => 0.089791691286
  | 5 => 0.090778502681
  | 6 => 0.091776780173
  | 7 => 0.092790561892
  | 8 => 0.093824563772
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12268 12268 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12268 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12268

/-! Actual upper energy certificates on all 43 source endpoints at 12268. -/
namespace BstLean.Part264b.N12268
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12268 cell12268)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12268 (gMinus 12268) (1 - (cell12268 i).lower) ≤ 1 ∧
    energyUpper 12268 (gMinus 12268) (BstLean.Part211.gPlus 12268)
      (finiteEnergy 12268 12268 0.011) (1 - (cell12268 i).lower) ≤
      (cell12268 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12268) (by norm_num)
        (q := 1 - (cell12268 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12268,cell12268]) (by norm_num [scalarRow12268,cell12268])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12268,cell12268])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12268

/-! Source-cell containment and simple scalar guards at 12268. -/
namespace BstLean.Part264b.N12268
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12268 cell12268)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12268 ⟨10,by decide⟩).lower ∧ (cell12268 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12268 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12268 ⟨11,by decide⟩).lower ∧ (cell12268 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12268 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12268 ⟨12,by decide⟩).lower ∧ (cell12268 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12268 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12268 ⟨13,by decide⟩).lower ∧ (cell12268 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12268 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12268 ⟨14,by decide⟩).lower ∧ (cell12268 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12268 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12268 ⟨15,by decide⟩).lower ∧ (cell12268 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12268 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12268 ⟨16,by decide⟩).lower ∧ (cell12268 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12268 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12268 ⟨17,by decide⟩).lower ∧ (cell12268 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12268 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12268 ⟨18,by decide⟩).lower ∧ (cell12268 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12268 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12268 ⟨19,by decide⟩).lower ∧ (cell12268 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12268 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12268 ⟨20,by decide⟩).lower ∧ (cell12268 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12268 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12268 ⟨21,by decide⟩).lower ∧ (cell12268 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12268 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12268 ⟨22,by decide⟩).lower ∧ (cell12268 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12268 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12268 ⟨23,by decide⟩).lower ∧ (cell12268 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12268 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12268 ⟨24,by decide⟩).lower ∧ (cell12268 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12268 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12268 ⟨25,by decide⟩).lower ∧ (cell12268 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12268 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12268 ⟨26,by decide⟩).lower ∧ (cell12268 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12268 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12268 ⟨27,by decide⟩).lower ∧ (cell12268 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12268 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12268 ⟨28,by decide⟩).lower ∧ (cell12268 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12268 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12268 ⟨29,by decide⟩).lower ∧ (cell12268 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12268 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12268 ⟨30,by decide⟩).lower ∧ (cell12268 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12268 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12268 ⟨31,by decide⟩).lower ∧ (cell12268 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12268 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12268 ⟨32,by decide⟩).lower ∧ (cell12268 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12268 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12268 ⟨33,by decide⟩).lower ∧ (cell12268 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12268 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12268 ⟨34,by decide⟩).lower ∧ (cell12268 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12268 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12268 ⟨35,by decide⟩).lower ∧ (cell12268 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12268 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12268 ⟨36,by decide⟩).lower ∧ (cell12268 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12268 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12268 ⟨37,by decide⟩).lower ∧ (cell12268 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12268 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12268 ⟨38,by decide⟩).lower ∧ (cell12268 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12268 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12268 ⟨39,by decide⟩).lower ∧ (cell12268 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12268 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12268 ⟨40,by decide⟩).lower ∧ (cell12268 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12268 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12268 ⟨41,by decide⟩).lower ∧ (cell12268 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12268 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12268 ⟨42,by decide⟩).lower ∧ (cell12268 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12268 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12268 ⟨43,by decide⟩).lower ∧ (cell12268 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12268 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12268 ⟨44,by decide⟩).lower ∧ (cell12268 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12268 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12268 ⟨45,by decide⟩).lower ∧ (cell12268 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12268 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12268 ⟨46,by decide⟩).lower ∧ (cell12268 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12268 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12268 ⟨47,by decide⟩).lower ∧ (cell12268 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12268 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12268 ⟨48,by decide⟩).lower ∧ (cell12268 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12268 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12268 ⟨49,by decide⟩).lower ∧ (cell12268 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12268 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12268 ⟨50,by decide⟩).lower ∧ (cell12268 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12268 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12268 ⟨51,by decide⟩).lower ∧ (cell12268 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12268 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12268 ⟨52,by decide⟩).lower ∧ (cell12268 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12268 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12268 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12268 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12268,cell12268,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12268 i).lower ∧
    (cell12268 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12268 i).upper ≤ (0.532 : ℝ) ∧
    (cell12268 i).centre ≤ (0.1 : ℝ) ∧ (cell12268 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12268 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12268 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12268

/-! The local source numeric instances at 12268 have no network premises. -/
namespace BstLean.Part264b.N12268
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12268 cell12268)

noncomputable def sourceNumerics12268 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12268 (cell12268 i)
      scalarRow12268.M scalarRow12268.H scalarRow12268.xi := by
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
    energy_allowance := scalarRow12268.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12268]
    centre_nonneg := (scalarRow12268.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12268]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12268
/-! Actual 12269 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12269
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12269 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12269 12269 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12269.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12269 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12269 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12269 := gPlus_lower 12269
end BstLean.Part264b.N12269

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12269
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036438346434 : ℝ) ≤ wn 12269 := by
  have hn : √(12269 : ℝ) ≤ 110.765518100175 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12269 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.765518100175 ≤ 2 / √12269 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260887600 : ℝ) ≤ rhoBar 12269 BstLean.Part154.csC ∧
    rhoBar 12269 BstLean.Part154.csC ≤ 0.000260904781 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036438346434 : ℝ) / (1.295212 * 12269) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12269) := by gcongr
      _ ≤ (0.000260904781 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12269 BstLean.Part154.csC) ≤ 0.001043687196 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12269 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12269 BstLean.Part154.csC) (piBar (rhoBar 12269 BstLean.Part154.csC)) ≤ 0.000199281164 ∧
    cc1 (rhoBar 12269 BstLean.Part154.csC) (piBar (rhoBar 12269 BstLean.Part154.csC)) ≤ 0.000126803859 ∧
    cc2 (rhoBar 12269 BstLean.Part154.csC) ≤ 0.000073610529 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12269 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12269 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12269 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12269 BstLean.Part154.csC * nuR (rhoBar 12269 BstLean.Part154.csC)) ≤ 0.000521826580 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260904781 : ℝ) * 0.001043687196 := by gcongr
      _ ≤ (0.000521826580 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12269 BstLean.Part154.csC) * nuR (rhoBar 12269 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043687196 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12269 BstLean.Part154.csC) * rhoBar 12269 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260904781 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260904781 / 2 + 0.399 * 0.001043687196 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199281164 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521826580 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126803859 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260904781 / 1.414213562 := by gcongr
      _ ≤ (0.000073610529 : ℝ) := by norm_num

end BstLean.Part264b.N12269

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12269
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12269 BstLean.Part154.csC) (piBar (rhoBar 12269 BstLean.Part154.csC)) ≤ 1.71501E-7 := by
  have hr0 : 0 ≤ rhoBar 12269 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12269 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12269 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12269 BstLean.Part154.csC) (piBar (rhoBar 12269 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12269 BstLean.Part154.csC) (piBar (rhoBar 12269 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12269 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199281164 : ℝ) ^ 2 + 0.000126803859 ^ 2 + 3 * 0.000073610529 ^ 2 +
        2 * 0.797885 * 0.000199281164 * 0.000126803859 + 2 * 0.000199281164 * 0.000073610529 +
        4 * 0.797885 * 0.000126803859 * 0.000073610529 := by gcongr
    _ ≤ (1.71501E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12269 BstLean.Part154.csC Θ ≤ 0.002725490120 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12269 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12269 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12269 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12269 BstLean.Part154.csC) (piBar (rhoBar 12269 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12269 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71501E-7 / (0.000260887600 : ℝ) := by gcongr
    _ ≤ 0.002725490120 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12269 BstLean.Part154.csC Θ ≤ 0.003025918098 + 0.000688642218 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12269 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12269 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12269 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260904781 +
        (6863 / 10000) * 0.000260904781 * 12269 * 0.001043687196) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003025918098 + 0.000688642218 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12269 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12269 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12269 0.011 Θ ∧ gammaRatio 12269 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12269 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12269) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12269 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12269 0.011 Θ) :=
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
    badAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12269 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12269 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12269 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12269 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12269 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12269 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12269 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12269 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12269 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12269 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12269 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004125918098 + 0.003414132338 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12269

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12269
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12269 BstLean.Part154.csC) (piBar (rhoBar 12269 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12269 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12269 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12269 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12269 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12269 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12269 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12269 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12269 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12269 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12269 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12269 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12269 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053408303984 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12269) ≤ 0.010781672867 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12269 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010781672867 + 2 * 0.737676 / 12269) := by gcongr
    _ ≤ (0.053408303984 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12269 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12269

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12269
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483392485 : ℝ) ≤ plow 12269 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12269) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424937576)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430882313) : eMP 12269 0.011 xi bn ≤ 0.001231150508 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12269 : ℝ) * (1 - 0.011))) ≤ 0.000608659198 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001430882313 / (12269 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608659198 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608659198 : ℝ) + 3.141593 * 0.053424937576 / (12269 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001231150508 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424937576)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430882313) : PiBarMP 12269 12 0.011 xi bn ≤ 0.164092712990 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12269 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037827005076 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.154623144015 : ℝ) ≤ √((12269 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.765518100174 : ℝ) ≤ √12269 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12269) ≤ 0.125782901590 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037827005076 + 0.053424937576 * 1.772454 / (2 * (110.154623144015 : ℝ))) * (1 + 0.001231150508) +
        8 / (12269 * 110.765518100174) + 0.125782901590 := by gcongr
    _ ≤ (0.164092712990 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424937576)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430882313) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284546655575) :
    parallelOracle 12269 0.011 xi bn cd ≤ 0.165120856027 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12269 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12269 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483392485 : ℝ) ≤ plow 12269 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.765518100174 : ℝ) ≤ √12269 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284546655575 : ℝ) / (2 * 0.560483392485 * 110.765518100174)) * 0.164092712990 +
        0.284546655575 ^ 2 / (2 * 0.560483392485 * 110.765518100174) := by gcongr
    _ ≤ (0.165120856027 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424937576) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430882313)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284546655575) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12269 12269 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483392485 : ℝ) ≤ plow 12269 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.765518100174 : ℝ) ≤ √12269 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12269 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12269 Θ 1.22 ≤ 0.011972141898 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.765518100174 := by gcongr <;> linarith
      _ ≤ (0.011972141898 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12269 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12269 12269 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12269 12269 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12269 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12269 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12269 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12269 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165120856027 + 0.011972141898 + (0.008646 : ℝ) *
        (1 + 2 * (0.284546655575 + 0.011972141898) / (0.560483392485 * 110.765518100174))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12269]

end BstLean.Part264b.N12269

/-! The original eight local profiles supply actual 12269 moment certificates. -/
namespace BstLean.Part264b.N12269
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12269 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053424937576 ∧
    0 ≤ bN 12269 BstLean.Part154.csC (groupTheta g) ∧ bN 12269 BstLean.Part154.csC (groupTheta g) ≤ 0.001430882313 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12269 12269 0.011
      (momentAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12269 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12269 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12269 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231138351591 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12269 0.011
      (momentAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12269 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12269
/-! The actual computed-centre upper energy formula at 12269. -/
namespace BstLean.Part264b.N12269
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12269

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12269
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12269 cell12269)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086864802936
  | 2 => 0.087835673977
  | 3 => 0.088809230365
  | 4 => 0.089787900410
  | 5 => 0.090774581489
  | 6 => 0.091772704347
  | 7 => 0.092786302488
  | 8 => 0.093820086560
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12269 12269 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12269 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12269

/-! Actual upper energy certificates on all 43 source endpoints at 12269. -/
namespace BstLean.Part264b.N12269
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12269 cell12269)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12269 (gMinus 12269) (1 - (cell12269 i).lower) ≤ 1 ∧
    energyUpper 12269 (gMinus 12269) (BstLean.Part211.gPlus 12269)
      (finiteEnergy 12269 12269 0.011) (1 - (cell12269 i).lower) ≤
      (cell12269 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12269) (by norm_num)
        (q := 1 - (cell12269 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12269,cell12269]) (by norm_num [scalarRow12269,cell12269])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12269,cell12269])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12269

/-! Source-cell containment and simple scalar guards at 12269. -/
namespace BstLean.Part264b.N12269
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12269 cell12269)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12269 ⟨10,by decide⟩).lower ∧ (cell12269 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12269 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12269 ⟨11,by decide⟩).lower ∧ (cell12269 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12269 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12269 ⟨12,by decide⟩).lower ∧ (cell12269 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12269 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12269 ⟨13,by decide⟩).lower ∧ (cell12269 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12269 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12269 ⟨14,by decide⟩).lower ∧ (cell12269 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12269 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12269 ⟨15,by decide⟩).lower ∧ (cell12269 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12269 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12269 ⟨16,by decide⟩).lower ∧ (cell12269 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12269 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12269 ⟨17,by decide⟩).lower ∧ (cell12269 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12269 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12269 ⟨18,by decide⟩).lower ∧ (cell12269 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12269 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12269 ⟨19,by decide⟩).lower ∧ (cell12269 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12269 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12269 ⟨20,by decide⟩).lower ∧ (cell12269 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12269 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12269 ⟨21,by decide⟩).lower ∧ (cell12269 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12269 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12269 ⟨22,by decide⟩).lower ∧ (cell12269 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12269 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12269 ⟨23,by decide⟩).lower ∧ (cell12269 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12269 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12269 ⟨24,by decide⟩).lower ∧ (cell12269 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12269 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12269 ⟨25,by decide⟩).lower ∧ (cell12269 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12269 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12269 ⟨26,by decide⟩).lower ∧ (cell12269 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12269 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12269 ⟨27,by decide⟩).lower ∧ (cell12269 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12269 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12269 ⟨28,by decide⟩).lower ∧ (cell12269 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12269 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12269 ⟨29,by decide⟩).lower ∧ (cell12269 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12269 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12269 ⟨30,by decide⟩).lower ∧ (cell12269 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12269 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12269 ⟨31,by decide⟩).lower ∧ (cell12269 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12269 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12269 ⟨32,by decide⟩).lower ∧ (cell12269 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12269 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12269 ⟨33,by decide⟩).lower ∧ (cell12269 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12269 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12269 ⟨34,by decide⟩).lower ∧ (cell12269 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12269 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12269 ⟨35,by decide⟩).lower ∧ (cell12269 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12269 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12269 ⟨36,by decide⟩).lower ∧ (cell12269 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12269 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12269 ⟨37,by decide⟩).lower ∧ (cell12269 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12269 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12269 ⟨38,by decide⟩).lower ∧ (cell12269 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12269 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12269 ⟨39,by decide⟩).lower ∧ (cell12269 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12269 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12269 ⟨40,by decide⟩).lower ∧ (cell12269 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12269 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12269 ⟨41,by decide⟩).lower ∧ (cell12269 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12269 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12269 ⟨42,by decide⟩).lower ∧ (cell12269 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12269 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12269 ⟨43,by decide⟩).lower ∧ (cell12269 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12269 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12269 ⟨44,by decide⟩).lower ∧ (cell12269 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12269 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12269 ⟨45,by decide⟩).lower ∧ (cell12269 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12269 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12269 ⟨46,by decide⟩).lower ∧ (cell12269 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12269 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12269 ⟨47,by decide⟩).lower ∧ (cell12269 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12269 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12269 ⟨48,by decide⟩).lower ∧ (cell12269 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12269 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12269 ⟨49,by decide⟩).lower ∧ (cell12269 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12269 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12269 ⟨50,by decide⟩).lower ∧ (cell12269 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12269 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12269 ⟨51,by decide⟩).lower ∧ (cell12269 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12269 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12269 ⟨52,by decide⟩).lower ∧ (cell12269 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12269 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12269 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12269 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12269,cell12269,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12269 i).lower ∧
    (cell12269 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12269 i).upper ≤ (0.532 : ℝ) ∧
    (cell12269 i).centre ≤ (0.1 : ℝ) ∧ (cell12269 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12269 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12269 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12269

/-! The local source numeric instances at 12269 have no network premises. -/
namespace BstLean.Part264b.N12269
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12269 cell12269)

noncomputable def sourceNumerics12269 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12269 (cell12269 i)
      scalarRow12269.M scalarRow12269.H scalarRow12269.xi := by
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
    energy_allowance := scalarRow12269.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12269]
    centre_nonneg := (scalarRow12269.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12269]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12269
/-! Actual 12270 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12270
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12270 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12270 12270 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12270.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12270 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12270 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12270 := gPlus_lower 12270
end BstLean.Part264b.N12270

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12270
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036436848263 : ℝ) ≤ wn 12270 := by
  have hn : √(12270 : ℝ) ≤ 110.770032048384 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12270 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.770032048384 ≤ 2 / √12270 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260865961 : ℝ) ≤ rhoBar 12270 BstLean.Part154.csC ∧
    rhoBar 12270 BstLean.Part154.csC ≤ 0.000260883518 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036436848263 : ℝ) / (1.295212 * 12270) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12270) := by gcongr
      _ ≤ (0.000260883518 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12270 BstLean.Part154.csC) ≤ 0.001043602133 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12270 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12270 BstLean.Part154.csC) (piBar (rhoBar 12270 BstLean.Part154.csC)) ≤ 0.000199264922 ∧
    cc1 (rhoBar 12270 BstLean.Part154.csC) (piBar (rhoBar 12270 BstLean.Part154.csC)) ≤ 0.000126793525 ∧
    cc2 (rhoBar 12270 BstLean.Part154.csC) ≤ 0.000073604530 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12270 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12270 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12270 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12270 BstLean.Part154.csC * nuR (rhoBar 12270 BstLean.Part154.csC)) ≤ 0.000521784051 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260883518 : ℝ) * 0.001043602133 := by gcongr
      _ ≤ (0.000521784051 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12270 BstLean.Part154.csC) * nuR (rhoBar 12270 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043602133 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12270 BstLean.Part154.csC) * rhoBar 12270 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260883518 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260883518 / 2 + 0.399 * 0.001043602133 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199264922 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521784051 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126793525 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260883518 / 1.414213562 := by gcongr
      _ ≤ (0.000073604530 : ℝ) := by norm_num

end BstLean.Part264b.N12270

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12270
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12270 BstLean.Part154.csC) (piBar (rhoBar 12270 BstLean.Part154.csC)) ≤ 1.71473E-7 := by
  have hr0 : 0 ≤ rhoBar 12270 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12270 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12270 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12270 BstLean.Part154.csC) (piBar (rhoBar 12270 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12270 BstLean.Part154.csC) (piBar (rhoBar 12270 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12270 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199264922 : ℝ) ^ 2 + 0.000126793525 ^ 2 + 3 * 0.000073604530 ^ 2 +
        2 * 0.797885 * 0.000199264922 * 0.000126793525 + 2 * 0.000199264922 * 0.000073604530 +
        4 * 0.797885 * 0.000126793525 * 0.000073604530 := by gcongr
    _ ≤ (1.71473E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12270 BstLean.Part154.csC Θ ≤ 0.002725271189 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12270 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12270 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12270 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12270 BstLean.Part154.csC) (piBar (rhoBar 12270 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12270 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71473E-7 / (0.000260865961 : ℝ) := by gcongr
    _ ≤ 0.002725271189 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12270 BstLean.Part154.csC Θ ≤ 0.003025671486 + 0.000688586095 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12270 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12270 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12270 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260883518 +
        (6863 / 10000) * 0.000260883518 * 12270 * 0.001043602133) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003025671486 + 0.000688586095 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12270 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12270 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12270 0.011 Θ ∧ gammaRatio 12270 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12270 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12270) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12270 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12270 0.011 Θ) :=
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
    badAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12270 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12270 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12270 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12270 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12270 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12270 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12270 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12270 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12270 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12270 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12270 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004125671486 + 0.003413857284 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12270

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12270
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12270 BstLean.Part154.csC) (piBar (rhoBar 12270 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12270 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12270 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12270 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12270 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12270 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12270 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12270 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12270 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12270 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12270 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12270 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12270 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053406103557 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12270) ≤ 0.010781233507 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12270 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010781233507 + 2 * 0.737676 / 12270) := by gcongr
    _ ≤ (0.053406103557 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12270 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12270

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12270
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483440937 : ℝ) ≤ plow 12270 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12270) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424546561)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430767375) : eMP 12270 0.011 xi bn ≤ 0.001231050782 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12270 : ℝ) * (1 - 0.011))) ≤ 0.000608609949 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001430767375 / (12270 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608609949 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608609949 : ℝ) + 3.141593 * 0.053424546561 / (12270 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001231050782 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424546561)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430767375) : PiBarMP 12270 12 0.011 xi bn ≤ 0.164086040877 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12270 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037825485787 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.159112196858 : ℝ) ≤ √((12270 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.770032048383 : ℝ) ≤ √12270 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12270) ≤ 0.125777775858 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037825485787 + 0.053424546561 * 1.772454 / (2 * (110.159112196858 : ℝ))) * (1 + 0.001231050782) +
        8 / (12270 * 110.770032048383) + 0.125777775858 := by gcongr
    _ ≤ (0.164086040877 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424546561)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430767375) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284543609300) :
    parallelOracle 12270 0.011 xi bn cd ≤ 0.165114108651 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12270 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12270 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483440937 : ℝ) ≤ plow 12270 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.770032048383 : ℝ) ≤ √12270 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284543609300 : ℝ) / (2 * 0.560483440937 * 110.770032048383)) * 0.164086040877 +
        0.284543609300 ^ 2 / (2 * 0.560483440937 * 110.770032048383) := by gcongr
    _ ≤ (0.165114108651 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424546561) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430767375)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284543609300) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12270 12270 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483440937 : ℝ) ≤ plow 12270 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.770032048383 : ℝ) ≤ √12270 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12270 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12270 Θ 1.22 ≤ 0.011971654025 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.770032048383 := by gcongr <;> linarith
      _ ≤ (0.011971654025 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12270 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12270 12270 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12270 12270 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12270 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12270 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12270 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12270 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165114108651 + 0.011971654025 + (0.008646 : ℝ) *
        (1 + 2 * (0.284543609300 + 0.011971654025) / (0.560483440937 * 110.770032048383))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12270]

end BstLean.Part264b.N12270

/-! The original eight local profiles supply actual 12270 moment certificates. -/
namespace BstLean.Part264b.N12270
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12270 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053424546561 ∧
    0 ≤ bN 12270 BstLean.Part154.csC (groupTheta g) ∧ bN 12270 BstLean.Part154.csC (groupTheta g) ≤ 0.001430767375 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12270 12270 0.011
      (momentAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12270 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12270 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12270 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231137505743 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12270 0.011
      (momentAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12270 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12270
/-! The actual computed-centre upper energy formula at 12270. -/
namespace BstLean.Part264b.N12270
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12270

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12270
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12270 cell12270)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086861296371
  | 2 => 0.087832088121
  | 3 => 0.088805551403
  | 4 => 0.089784111544
  | 5 => 0.090770662451
  | 6 => 0.091768630848
  | 7 => 0.092782045620
  | 8 => 0.093815612133
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12270 12270 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12270 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12270

/-! Actual upper energy certificates on all 43 source endpoints at 12270. -/
namespace BstLean.Part264b.N12270
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12270 cell12270)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12270 (gMinus 12270) (1 - (cell12270 i).lower) ≤ 1 ∧
    energyUpper 12270 (gMinus 12270) (BstLean.Part211.gPlus 12270)
      (finiteEnergy 12270 12270 0.011) (1 - (cell12270 i).lower) ≤
      (cell12270 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12270) (by norm_num)
        (q := 1 - (cell12270 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12270,cell12270]) (by norm_num [scalarRow12270,cell12270])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12270,cell12270])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12270

/-! Source-cell containment and simple scalar guards at 12270. -/
namespace BstLean.Part264b.N12270
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12270 cell12270)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12270 ⟨10,by decide⟩).lower ∧ (cell12270 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12270 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12270 ⟨11,by decide⟩).lower ∧ (cell12270 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12270 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12270 ⟨12,by decide⟩).lower ∧ (cell12270 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12270 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12270 ⟨13,by decide⟩).lower ∧ (cell12270 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12270 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12270 ⟨14,by decide⟩).lower ∧ (cell12270 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12270 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12270 ⟨15,by decide⟩).lower ∧ (cell12270 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12270 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12270 ⟨16,by decide⟩).lower ∧ (cell12270 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12270 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12270 ⟨17,by decide⟩).lower ∧ (cell12270 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12270 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12270 ⟨18,by decide⟩).lower ∧ (cell12270 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12270 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12270 ⟨19,by decide⟩).lower ∧ (cell12270 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12270 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12270 ⟨20,by decide⟩).lower ∧ (cell12270 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12270 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12270 ⟨21,by decide⟩).lower ∧ (cell12270 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12270 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12270 ⟨22,by decide⟩).lower ∧ (cell12270 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12270 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12270 ⟨23,by decide⟩).lower ∧ (cell12270 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12270 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12270 ⟨24,by decide⟩).lower ∧ (cell12270 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12270 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12270 ⟨25,by decide⟩).lower ∧ (cell12270 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12270 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12270 ⟨26,by decide⟩).lower ∧ (cell12270 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12270 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12270 ⟨27,by decide⟩).lower ∧ (cell12270 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12270 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12270 ⟨28,by decide⟩).lower ∧ (cell12270 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12270 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12270 ⟨29,by decide⟩).lower ∧ (cell12270 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12270 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12270 ⟨30,by decide⟩).lower ∧ (cell12270 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12270 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12270 ⟨31,by decide⟩).lower ∧ (cell12270 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12270 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12270 ⟨32,by decide⟩).lower ∧ (cell12270 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12270 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12270 ⟨33,by decide⟩).lower ∧ (cell12270 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12270 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12270 ⟨34,by decide⟩).lower ∧ (cell12270 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12270 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12270 ⟨35,by decide⟩).lower ∧ (cell12270 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12270 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12270 ⟨36,by decide⟩).lower ∧ (cell12270 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12270 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12270 ⟨37,by decide⟩).lower ∧ (cell12270 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12270 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12270 ⟨38,by decide⟩).lower ∧ (cell12270 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12270 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12270 ⟨39,by decide⟩).lower ∧ (cell12270 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12270 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12270 ⟨40,by decide⟩).lower ∧ (cell12270 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12270 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12270 ⟨41,by decide⟩).lower ∧ (cell12270 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12270 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12270 ⟨42,by decide⟩).lower ∧ (cell12270 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12270 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12270 ⟨43,by decide⟩).lower ∧ (cell12270 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12270 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12270 ⟨44,by decide⟩).lower ∧ (cell12270 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12270 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12270 ⟨45,by decide⟩).lower ∧ (cell12270 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12270 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12270 ⟨46,by decide⟩).lower ∧ (cell12270 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12270 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12270 ⟨47,by decide⟩).lower ∧ (cell12270 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12270 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12270 ⟨48,by decide⟩).lower ∧ (cell12270 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12270 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12270 ⟨49,by decide⟩).lower ∧ (cell12270 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12270 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12270 ⟨50,by decide⟩).lower ∧ (cell12270 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12270 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12270 ⟨51,by decide⟩).lower ∧ (cell12270 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12270 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12270 ⟨52,by decide⟩).lower ∧ (cell12270 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12270 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12270 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12270 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12270,cell12270,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12270 i).lower ∧
    (cell12270 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12270 i).upper ≤ (0.532 : ℝ) ∧
    (cell12270 i).centre ≤ (0.1 : ℝ) ∧ (cell12270 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12270 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12270 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12270

/-! The local source numeric instances at 12270 have no network premises. -/
namespace BstLean.Part264b.N12270
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12270 cell12270)

noncomputable def sourceNumerics12270 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12270 (cell12270 i)
      scalarRow12270.M scalarRow12270.H scalarRow12270.xi := by
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
    energy_allowance := scalarRow12270.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12270]
    centre_nonneg := (scalarRow12270.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12270]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12270
/-! Actual 12271 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12271
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12271 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12271 12271 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12271.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12271 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12271 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12271 := gPlus_lower 12271
end BstLean.Part264b.N12271

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12271
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036435350277 : ℝ) ≤ wn 12271 := by
  have hn : √(12271 : ℝ) ≤ 110.774545812655 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12271 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.774545812655 ≤ 2 / √12271 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260844325 : ℝ) ≤ rhoBar 12271 BstLean.Part154.csC ∧
    rhoBar 12271 BstLean.Part154.csC ≤ 0.000260862258 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036435350277 : ℝ) / (1.295212 * 12271) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12271) := by gcongr
      _ ≤ (0.000260862258 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12271 BstLean.Part154.csC) ≤ 0.001043517082 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12271 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12271 BstLean.Part154.csC) (piBar (rhoBar 12271 BstLean.Part154.csC)) ≤ 0.000199248683 ∧
    cc1 (rhoBar 12271 BstLean.Part154.csC) (piBar (rhoBar 12271 BstLean.Part154.csC)) ≤ 0.000126783192 ∧
    cc2 (rhoBar 12271 BstLean.Part154.csC) ≤ 0.000073598532 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12271 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12271 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12271 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12271 BstLean.Part154.csC * nuR (rhoBar 12271 BstLean.Part154.csC)) ≤ 0.000521741529 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260862258 : ℝ) * 0.001043517082 := by gcongr
      _ ≤ (0.000521741529 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12271 BstLean.Part154.csC) * nuR (rhoBar 12271 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043517082 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12271 BstLean.Part154.csC) * rhoBar 12271 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260862258 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260862258 / 2 + 0.399 * 0.001043517082 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199248683 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521741529 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126783192 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260862258 / 1.414213562 := by gcongr
      _ ≤ (0.000073598532 : ℝ) := by norm_num

end BstLean.Part264b.N12271

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12271
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12271 BstLean.Part154.csC) (piBar (rhoBar 12271 BstLean.Part154.csC)) ≤ 1.71445E-7 := by
  have hr0 : 0 ≤ rhoBar 12271 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12271 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12271 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12271 BstLean.Part154.csC) (piBar (rhoBar 12271 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12271 BstLean.Part154.csC) (piBar (rhoBar 12271 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12271 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199248683 : ℝ) ^ 2 + 0.000126783192 ^ 2 + 3 * 0.000073598532 ^ 2 +
        2 * 0.797885 * 0.000199248683 * 0.000126783192 + 2 * 0.000199248683 * 0.000073598532 +
        4 * 0.797885 * 0.000126783192 * 0.000073598532 := by gcongr
    _ ≤ (1.71445E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12271 BstLean.Part154.csC Θ ≤ 0.002725052190 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12271 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12271 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12271 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12271 BstLean.Part154.csC) (piBar (rhoBar 12271 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12271 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71445E-7 / (0.000260844325 : ℝ) := by gcongr
    _ ≤ 0.002725052190 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12271 BstLean.Part154.csC Θ ≤ 0.003025424903 + 0.000688529981 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12271 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12271 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12271 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260862258 +
        (6863 / 10000) * 0.000260862258 * 12271 * 0.001043517082) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003025424903 + 0.000688529981 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12271 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12271 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12271 0.011 Θ ∧ gammaRatio 12271 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12271 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12271) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12271 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12271 0.011 Θ) :=
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
    badAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12271 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12271 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12271 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12271 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12271 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12271 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12271 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12271 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12271 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12271 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12271 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004125424903 + 0.003413582171 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12271

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12271
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12271 BstLean.Part154.csC) (piBar (rhoBar 12271 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12271 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12271 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12271 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12271 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12271 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12271 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12271 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12271 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12271 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12271 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12271 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12271 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053403903401 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12271) ≤ 0.010780794201 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12271 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010780794201 + 2 * 0.737676 / 12271) := by gcongr
    _ ≤ (0.053403903401 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12271 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12271

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12271
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483489381 : ℝ) ≤ plow 12271 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12271) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424155543)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430652400) : eMP 12271 0.011 xi bn ≤ 0.001230951049 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12271 : ℝ) * (1 - 0.011))) ≤ 0.000608560697 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001430652400 / (12271 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608560697 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608560697 : ℝ) + 3.141593 * 0.053424155543 / (12271 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001230951049 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424155543)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430652400) : PiBarMP 12271 12 0.011 xi bn ≤ 0.164079368843 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12271 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037823965948 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.163601066777 : ℝ) ≤ √((12271 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.774545812654 : ℝ) ≤ √12271 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12271) ≤ 0.125772650753 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037823965948 + 0.053424155543 * 1.772454 / (2 * (110.163601066777 : ℝ))) * (1 + 0.001230951049) +
        8 / (12271 * 110.774545812654) + 0.125772650753 := by gcongr
    _ ≤ (0.164079368843 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424155543)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430652400) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284540563287) :
    parallelOracle 12271 0.011 xi bn cd ≤ 0.165107361364 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12271 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12271 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483489381 : ℝ) ≤ plow 12271 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.774545812654 : ℝ) ≤ √12271 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284540563287 : ℝ) / (2 * 0.560483489381 * 110.774545812654)) * 0.164079368843 +
        0.284540563287 ^ 2 / (2 * 0.560483489381 * 110.774545812654) := by gcongr
    _ ≤ (0.165107361364 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053424155543) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430652400)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284540563287) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12271 12271 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483489381 : ℝ) ≤ plow 12271 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.774545812654 : ℝ) ≤ √12271 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12271 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12271 Θ 1.22 ≤ 0.011971166213 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.774545812654 := by gcongr <;> linarith
      _ ≤ (0.011971166213 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12271 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12271 12271 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12271 12271 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12271 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12271 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12271 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12271 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165107361364 + 0.011971166213 + (0.008646 : ℝ) *
        (1 + 2 * (0.284540563287 + 0.011971166213) / (0.560483489381 * 110.774545812654))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12271]

end BstLean.Part264b.N12271

/-! The original eight local profiles supply actual 12271 moment certificates. -/
namespace BstLean.Part264b.N12271
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12271 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053424155543 ∧
    0 ≤ bN 12271 BstLean.Part154.csC (groupTheta g) ∧ bN 12271 BstLean.Part154.csC (groupTheta g) ≤ 0.001430652400 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12271 12271 0.011
      (momentAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12271 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12271 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12271 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231136659886 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12271 0.011
      (momentAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12271 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12271
/-! The actual computed-centre upper energy formula at 12271. -/
namespace BstLean.Part264b.N12271
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12271

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12271
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12271 cell12271)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086857791523
  | 2 => 0.087828504060
  | 3 => 0.088801874332
  | 4 => 0.089780324687
  | 5 => 0.090766745564
  | 6 => 0.091764559674
  | 7 => 0.092777791285
  | 8 => 0.093811140489
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12271 12271 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12271 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12271

/-! Actual upper energy certificates on all 43 source endpoints at 12271. -/
namespace BstLean.Part264b.N12271
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12271 cell12271)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12271 (gMinus 12271) (1 - (cell12271 i).lower) ≤ 1 ∧
    energyUpper 12271 (gMinus 12271) (BstLean.Part211.gPlus 12271)
      (finiteEnergy 12271 12271 0.011) (1 - (cell12271 i).lower) ≤
      (cell12271 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12271) (by norm_num)
        (q := 1 - (cell12271 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12271,cell12271]) (by norm_num [scalarRow12271,cell12271])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12271,cell12271])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12271

/-! Source-cell containment and simple scalar guards at 12271. -/
namespace BstLean.Part264b.N12271
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12271 cell12271)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12271 ⟨10,by decide⟩).lower ∧ (cell12271 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12271 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12271 ⟨11,by decide⟩).lower ∧ (cell12271 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12271 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12271 ⟨12,by decide⟩).lower ∧ (cell12271 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12271 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12271 ⟨13,by decide⟩).lower ∧ (cell12271 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12271 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12271 ⟨14,by decide⟩).lower ∧ (cell12271 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12271 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12271 ⟨15,by decide⟩).lower ∧ (cell12271 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12271 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12271 ⟨16,by decide⟩).lower ∧ (cell12271 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12271 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12271 ⟨17,by decide⟩).lower ∧ (cell12271 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12271 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12271 ⟨18,by decide⟩).lower ∧ (cell12271 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12271 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12271 ⟨19,by decide⟩).lower ∧ (cell12271 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12271 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12271 ⟨20,by decide⟩).lower ∧ (cell12271 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12271 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12271 ⟨21,by decide⟩).lower ∧ (cell12271 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12271 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12271 ⟨22,by decide⟩).lower ∧ (cell12271 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12271 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12271 ⟨23,by decide⟩).lower ∧ (cell12271 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12271 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12271 ⟨24,by decide⟩).lower ∧ (cell12271 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12271 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12271 ⟨25,by decide⟩).lower ∧ (cell12271 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12271 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12271 ⟨26,by decide⟩).lower ∧ (cell12271 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12271 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12271 ⟨27,by decide⟩).lower ∧ (cell12271 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12271 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12271 ⟨28,by decide⟩).lower ∧ (cell12271 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12271 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12271 ⟨29,by decide⟩).lower ∧ (cell12271 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12271 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12271 ⟨30,by decide⟩).lower ∧ (cell12271 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12271 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12271 ⟨31,by decide⟩).lower ∧ (cell12271 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12271 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12271 ⟨32,by decide⟩).lower ∧ (cell12271 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12271 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12271 ⟨33,by decide⟩).lower ∧ (cell12271 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12271 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12271 ⟨34,by decide⟩).lower ∧ (cell12271 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12271 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12271 ⟨35,by decide⟩).lower ∧ (cell12271 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12271 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12271 ⟨36,by decide⟩).lower ∧ (cell12271 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12271 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12271 ⟨37,by decide⟩).lower ∧ (cell12271 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12271 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12271 ⟨38,by decide⟩).lower ∧ (cell12271 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12271 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12271 ⟨39,by decide⟩).lower ∧ (cell12271 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12271 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12271 ⟨40,by decide⟩).lower ∧ (cell12271 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12271 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12271 ⟨41,by decide⟩).lower ∧ (cell12271 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12271 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12271 ⟨42,by decide⟩).lower ∧ (cell12271 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12271 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12271 ⟨43,by decide⟩).lower ∧ (cell12271 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12271 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12271 ⟨44,by decide⟩).lower ∧ (cell12271 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12271 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12271 ⟨45,by decide⟩).lower ∧ (cell12271 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12271 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12271 ⟨46,by decide⟩).lower ∧ (cell12271 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12271 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12271 ⟨47,by decide⟩).lower ∧ (cell12271 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12271 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12271 ⟨48,by decide⟩).lower ∧ (cell12271 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12271 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12271 ⟨49,by decide⟩).lower ∧ (cell12271 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12271 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12271 ⟨50,by decide⟩).lower ∧ (cell12271 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12271 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12271 ⟨51,by decide⟩).lower ∧ (cell12271 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12271 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12271 ⟨52,by decide⟩).lower ∧ (cell12271 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12271 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12271 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12271 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12271,cell12271,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12271 i).lower ∧
    (cell12271 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12271 i).upper ≤ (0.532 : ℝ) ∧
    (cell12271 i).centre ≤ (0.1 : ℝ) ∧ (cell12271 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12271 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12271 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12271

/-! The local source numeric instances at 12271 have no network premises. -/
namespace BstLean.Part264b.N12271
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12271 cell12271)

noncomputable def sourceNumerics12271 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12271 (cell12271 i)
      scalarRow12271.M scalarRow12271.H scalarRow12271.xi := by
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
    energy_allowance := scalarRow12271.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12271]
    centre_nonneg := (scalarRow12271.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12271]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12271
/-! Actual 12272 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12272
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12272 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12272 12272 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12272.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12272 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12272 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12272 := gPlus_lower 12272
end BstLean.Part264b.N12272

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12272
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036433852474 : ℝ) ≤ wn 12272 := by
  have hn : √(12272 : ℝ) ≤ 110.779059393010 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12272 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.779059393010 ≤ 2 / √12272 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260822693 : ℝ) ≤ rhoBar 12272 BstLean.Part154.csC ∧
    rhoBar 12272 BstLean.Part154.csC ≤ 0.000260841001 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036433852474 : ℝ) / (1.295212 * 12272) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12272) := by gcongr
      _ ≤ (0.000260841001 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12272 BstLean.Part154.csC) ≤ 0.001043432043 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12272 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12272 BstLean.Part154.csC) (piBar (rhoBar 12272 BstLean.Part154.csC)) ≤ 0.000199232446 ∧
    cc1 (rhoBar 12272 BstLean.Part154.csC) (piBar (rhoBar 12272 BstLean.Part154.csC)) ≤ 0.000126772860 ∧
    cc2 (rhoBar 12272 BstLean.Part154.csC) ≤ 0.000073592534 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12272 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12272 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12272 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12272 BstLean.Part154.csC * nuR (rhoBar 12272 BstLean.Part154.csC)) ≤ 0.000521699012 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260841001 : ℝ) * 0.001043432043 := by gcongr
      _ ≤ (0.000521699012 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12272 BstLean.Part154.csC) * nuR (rhoBar 12272 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043432043 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12272 BstLean.Part154.csC) * rhoBar 12272 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260841001 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260841001 / 2 + 0.399 * 0.001043432043 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199232446 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521699012 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126772860 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260841001 / 1.414213562 := by gcongr
      _ ≤ (0.000073592534 : ℝ) := by norm_num

end BstLean.Part264b.N12272

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12272
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12272 BstLean.Part154.csC) (piBar (rhoBar 12272 BstLean.Part154.csC)) ≤ 1.71417E-7 := by
  have hr0 : 0 ≤ rhoBar 12272 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12272 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12272 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12272 BstLean.Part154.csC) (piBar (rhoBar 12272 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12272 BstLean.Part154.csC) (piBar (rhoBar 12272 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12272 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199232446 : ℝ) ^ 2 + 0.000126772860 ^ 2 + 3 * 0.000073592534 ^ 2 +
        2 * 0.797885 * 0.000199232446 * 0.000126772860 + 2 * 0.000199232446 * 0.000073592534 +
        4 * 0.797885 * 0.000126772860 * 0.000073592534 := by gcongr
    _ ≤ (1.71417E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12272 BstLean.Part154.csC Θ ≤ 0.002724833113 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12272 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12272 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12272 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12272 BstLean.Part154.csC) (piBar (rhoBar 12272 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12272 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71417E-7 / (0.000260822693 : ℝ) := by gcongr
    _ ≤ 0.002724833113 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12272 BstLean.Part154.csC Θ ≤ 0.003025178350 + 0.000688473874 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12272 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12272 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12272 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260841001 +
        (6863 / 10000) * 0.000260841001 * 12272 * 0.001043432043) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003025178350 + 0.000688473874 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12272 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12272 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12272 0.011 Θ ∧ gammaRatio 12272 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12272 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12272) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12272 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12272 0.011 Θ) :=
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
    badAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12272 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12272 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12272 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12272 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12272 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12272 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12272 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12272 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12272 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12272 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12272 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004125178350 + 0.003413306987 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12272

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12272
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12272 BstLean.Part154.csC) (piBar (rhoBar 12272 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12272 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12272 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12272 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12272 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12272 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12272 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12272 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12272 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12272 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12272 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12272 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12272 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053401703514 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12272) ≤ 0.010780354948 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12272 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010780354948 + 2 * 0.737676 / 12272) := by gcongr
    _ ≤ (0.053401703514 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12272 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12272

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12272
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483537817 : ℝ) ≤ plow 12272 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12272) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053423764519)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430537385) : eMP 12272 0.011 xi bn ≤ 0.001230851307 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12272 : ℝ) * (1 - 0.011))) ≤ 0.000608511440 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001430537385 / (12272 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608511440 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608511440 : ℝ) + 3.141593 * 0.053423764519 / (12272 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001230851307 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053423764519)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430537385) : PiBarMP 12272 12 0.011 xi bn ≤ 0.164072696847 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12272 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037822445519 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.168089753793 : ℝ) ≤ √((12272 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.779059393009 : ℝ) ≤ √12272 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12272) ≤ 0.125767526274 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037822445519 + 0.053423764519 * 1.772454 / (2 * (110.168089753793 : ℝ))) * (1 + 0.001230851307) +
        8 / (12272 * 110.779059393009) + 0.125767526274 := by gcongr
    _ ≤ (0.164072696847 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053423764519)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430537385) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284537517527) :
    parallelOracle 12272 0.011 xi bn cd ≤ 0.165100614125 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12272 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12272 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483537817 : ℝ) ≤ plow 12272 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.779059393009 : ℝ) ≤ √12272 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284537517527 : ℝ) / (2 * 0.560483537817 * 110.779059393009)) * 0.164072696847 +
        0.284537517527 ^ 2 / (2 * 0.560483537817 * 110.779059393009) := by gcongr
    _ ≤ (0.165100614125 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053423764519) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430537385)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284537517527) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12272 12272 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483537817 : ℝ) ≤ plow 12272 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.779059393009 : ℝ) ≤ √12272 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12272 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12272 Θ 1.22 ≤ 0.011970678460 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.779059393009 := by gcongr <;> linarith
      _ ≤ (0.011970678460 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12272 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12272 12272 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12272 12272 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12272 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12272 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12272 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12272 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165100614125 + 0.011970678460 + (0.008646 : ℝ) *
        (1 + 2 * (0.284537517527 + 0.011970678460) / (0.560483537817 * 110.779059393009))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12272]

end BstLean.Part264b.N12272

/-! The original eight local profiles supply actual 12272 moment certificates. -/
namespace BstLean.Part264b.N12272
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12272 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053423764519 ∧
    0 ≤ bN 12272 BstLean.Part154.csC (groupTheta g) ∧ bN 12272 BstLean.Part154.csC (groupTheta g) ≤ 0.001430537385 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12272 12272 0.011
      (momentAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12272 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12272 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12272 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231135814013 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12272 0.011
      (momentAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12272 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12272
/-! The actual computed-centre upper energy formula at 12272. -/
namespace BstLean.Part264b.N12272
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12272

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12272
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12272 cell12272)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086854288389
  | 2 => 0.087824921791
  | 3 => 0.088798199149
  | 4 => 0.089776539836
  | 5 => 0.090762830827
  | 6 => 0.091760490823
  | 7 => 0.092773539481
  | 8 => 0.093806671623
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12272 12272 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12272 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12272

/-! Actual upper energy certificates on all 43 source endpoints at 12272. -/
namespace BstLean.Part264b.N12272
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12272 cell12272)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12272 (gMinus 12272) (1 - (cell12272 i).lower) ≤ 1 ∧
    energyUpper 12272 (gMinus 12272) (BstLean.Part211.gPlus 12272)
      (finiteEnergy 12272 12272 0.011) (1 - (cell12272 i).lower) ≤
      (cell12272 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12272) (by norm_num)
        (q := 1 - (cell12272 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12272,cell12272]) (by norm_num [scalarRow12272,cell12272])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12272,cell12272])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12272

/-! Source-cell containment and simple scalar guards at 12272. -/
namespace BstLean.Part264b.N12272
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12272 cell12272)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12272 ⟨10,by decide⟩).lower ∧ (cell12272 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12272 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12272 ⟨11,by decide⟩).lower ∧ (cell12272 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12272 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12272 ⟨12,by decide⟩).lower ∧ (cell12272 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12272 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12272 ⟨13,by decide⟩).lower ∧ (cell12272 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12272 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12272 ⟨14,by decide⟩).lower ∧ (cell12272 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12272 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12272 ⟨15,by decide⟩).lower ∧ (cell12272 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12272 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12272 ⟨16,by decide⟩).lower ∧ (cell12272 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12272 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12272 ⟨17,by decide⟩).lower ∧ (cell12272 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12272 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12272 ⟨18,by decide⟩).lower ∧ (cell12272 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12272 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12272 ⟨19,by decide⟩).lower ∧ (cell12272 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12272 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12272 ⟨20,by decide⟩).lower ∧ (cell12272 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12272 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12272 ⟨21,by decide⟩).lower ∧ (cell12272 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12272 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12272 ⟨22,by decide⟩).lower ∧ (cell12272 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12272 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12272 ⟨23,by decide⟩).lower ∧ (cell12272 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12272 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12272 ⟨24,by decide⟩).lower ∧ (cell12272 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12272 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12272 ⟨25,by decide⟩).lower ∧ (cell12272 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12272 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12272 ⟨26,by decide⟩).lower ∧ (cell12272 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12272 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12272 ⟨27,by decide⟩).lower ∧ (cell12272 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12272 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12272 ⟨28,by decide⟩).lower ∧ (cell12272 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12272 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12272 ⟨29,by decide⟩).lower ∧ (cell12272 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12272 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12272 ⟨30,by decide⟩).lower ∧ (cell12272 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12272 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12272 ⟨31,by decide⟩).lower ∧ (cell12272 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12272 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12272 ⟨32,by decide⟩).lower ∧ (cell12272 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12272 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12272 ⟨33,by decide⟩).lower ∧ (cell12272 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12272 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12272 ⟨34,by decide⟩).lower ∧ (cell12272 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12272 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12272 ⟨35,by decide⟩).lower ∧ (cell12272 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12272 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12272 ⟨36,by decide⟩).lower ∧ (cell12272 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12272 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12272 ⟨37,by decide⟩).lower ∧ (cell12272 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12272 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12272 ⟨38,by decide⟩).lower ∧ (cell12272 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12272 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12272 ⟨39,by decide⟩).lower ∧ (cell12272 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12272 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12272 ⟨40,by decide⟩).lower ∧ (cell12272 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12272 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12272 ⟨41,by decide⟩).lower ∧ (cell12272 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12272 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12272 ⟨42,by decide⟩).lower ∧ (cell12272 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12272 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12272 ⟨43,by decide⟩).lower ∧ (cell12272 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12272 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12272 ⟨44,by decide⟩).lower ∧ (cell12272 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12272 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12272 ⟨45,by decide⟩).lower ∧ (cell12272 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12272 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12272 ⟨46,by decide⟩).lower ∧ (cell12272 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12272 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12272 ⟨47,by decide⟩).lower ∧ (cell12272 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12272 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12272 ⟨48,by decide⟩).lower ∧ (cell12272 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12272 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12272 ⟨49,by decide⟩).lower ∧ (cell12272 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12272 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12272 ⟨50,by decide⟩).lower ∧ (cell12272 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12272 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12272 ⟨51,by decide⟩).lower ∧ (cell12272 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12272 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12272 ⟨52,by decide⟩).lower ∧ (cell12272 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12272 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12272 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12272 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12272,cell12272,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12272 i).lower ∧
    (cell12272 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12272 i).upper ≤ (0.532 : ℝ) ∧
    (cell12272 i).centre ≤ (0.1 : ℝ) ∧ (cell12272 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12272 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12272 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12272

/-! The local source numeric instances at 12272 have no network premises. -/
namespace BstLean.Part264b.N12272
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12272 cell12272)

noncomputable def sourceNumerics12272 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12272 (cell12272 i)
      scalarRow12272.M scalarRow12272.H scalarRow12272.xi := by
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
    energy_allowance := scalarRow12272.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12272]
    centre_nonneg := (scalarRow12272.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12272]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12272
/-! Actual 12273 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12273
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12273 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12273 12273 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12273.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12273 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12273 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12273 := gPlus_lower 12273
end BstLean.Part264b.N12273

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12273
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036432354856 : ℝ) ≤ wn 12273 := by
  have hn : √(12273 : ℝ) ≤ 110.783572789471 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12273 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.783572789471 ≤ 2 / √12273 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260801064 : ℝ) ≤ rhoBar 12273 BstLean.Part154.csC ∧
    rhoBar 12273 BstLean.Part154.csC ≤ 0.000260819748 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036432354856 : ℝ) / (1.295212 * 12273) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12273) := by gcongr
      _ ≤ (0.000260819748 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12273 BstLean.Part154.csC) ≤ 0.001043347019 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12273 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12273 BstLean.Part154.csC) (piBar (rhoBar 12273 BstLean.Part154.csC)) ≤ 0.000199216212 ∧
    cc1 (rhoBar 12273 BstLean.Part154.csC) (piBar (rhoBar 12273 BstLean.Part154.csC)) ≤ 0.000126762531 ∧
    cc2 (rhoBar 12273 BstLean.Part154.csC) ≤ 0.000073586538 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12273 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12273 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12273 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12273 BstLean.Part154.csC * nuR (rhoBar 12273 BstLean.Part154.csC)) ≤ 0.000521656503 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260819748 : ℝ) * 0.001043347019 := by gcongr
      _ ≤ (0.000521656503 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12273 BstLean.Part154.csC) * nuR (rhoBar 12273 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043347019 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12273 BstLean.Part154.csC) * rhoBar 12273 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260819748 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260819748 / 2 + 0.399 * 0.001043347019 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199216212 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521656503 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126762531 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260819748 / 1.414213562 := by gcongr
      _ ≤ (0.000073586538 : ℝ) := by norm_num

end BstLean.Part264b.N12273

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12273
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12273 BstLean.Part154.csC) (piBar (rhoBar 12273 BstLean.Part154.csC)) ≤ 1.71389E-7 := by
  have hr0 : 0 ≤ rhoBar 12273 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12273 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12273 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12273 BstLean.Part154.csC) (piBar (rhoBar 12273 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12273 BstLean.Part154.csC) (piBar (rhoBar 12273 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12273 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199216212 : ℝ) ^ 2 + 0.000126762531 ^ 2 + 3 * 0.000073586538 ^ 2 +
        2 * 0.797885 * 0.000199216212 * 0.000126762531 + 2 * 0.000199216212 * 0.000073586538 +
        4 * 0.797885 * 0.000126762531 * 0.000073586538 := by gcongr
    _ ≤ (1.71389E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12273 BstLean.Part154.csC Θ ≤ 0.002724613968 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12273 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12273 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12273 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12273 BstLean.Part154.csC) (piBar (rhoBar 12273 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12273 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71389E-7 / (0.000260801064 : ℝ) := by gcongr
    _ ≤ 0.002724613968 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12273 BstLean.Part154.csC Θ ≤ 0.003024931846 + 0.000688417778 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12273 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12273 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12273 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260819748 +
        (6863 / 10000) * 0.000260819748 * 12273 * 0.001043347019) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003024931846 + 0.000688417778 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12273 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12273 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12273 0.011 Θ ∧ gammaRatio 12273 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12273 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12273) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12273 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12273 0.011 Θ) :=
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
    badAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12273 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12273 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12273 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12273 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12273 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12273 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12273 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12273 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12273 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12273 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12273 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004124931846 + 0.003413031746 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12273

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12273
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12273 BstLean.Part154.csC) (piBar (rhoBar 12273 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12273 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12273 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12273 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12273 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12273 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12273 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12273 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12273 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12273 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12273 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12273 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12273 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053399503903 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12273) ≤ 0.010779915750 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12273 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010779915750 + 2 * 0.737676 / 12273) := by gcongr
    _ ≤ (0.053399503903 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12273 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12273

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12273
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483586246 : ℝ) ≤ plow 12273 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12273) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053423373513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430422334) : eMP 12273 0.011 xi bn ≤ 0.001230751559 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12273 : ℝ) * (1 - 0.011))) ≤ 0.000608462180 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001430422334 / (12273 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608462180 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608462180 : ℝ) + 3.141593 * 0.053423373513 / (12273 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001230751559 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053423373513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430422334) : PiBarMP 12273 12 0.011 xi bn ≤ 0.164066024942 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12273 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037820924553 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.172578257931 : ℝ) ≤ √((12273 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.783572789470 : ℝ) ≤ √12273 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12273) ≤ 0.125762402421 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037820924553 + 0.053423373513 * 1.772454 / (2 * (110.172578257931 : ℝ))) * (1 + 0.001230751559) +
        8 / (12273 * 110.783572789470) + 0.125762402421 := by gcongr
    _ ≤ (0.164066024942 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053423373513)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430422334) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284534472078) :
    parallelOracle 12273 0.011 xi bn cd ≤ 0.165093866987 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12273 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12273 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483586246 : ℝ) ≤ plow 12273 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.783572789470 : ℝ) ≤ √12273 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284534472078 : ℝ) / (2 * 0.560483586246 * 110.783572789470)) * 0.164066024942 +
        0.284534472078 ^ 2 / (2 * 0.560483586246 * 110.783572789470) := by gcongr
    _ ≤ (0.165093866987 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053423373513) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430422334)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284534472078) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12273 12273 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483586246 : ℝ) ≤ plow 12273 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.783572789470 : ℝ) ≤ √12273 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12273 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12273 Θ 1.22 ≤ 0.011970190766 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.783572789470 := by gcongr <;> linarith
      _ ≤ (0.011970190766 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12273 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12273 12273 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12273 12273 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12273 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12273 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12273 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12273 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165093866987 + 0.011970190766 + (0.008646 : ℝ) *
        (1 + 2 * (0.284534472078 + 0.011970190766) / (0.560483586246 * 110.783572789470))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12273]

end BstLean.Part264b.N12273

/-! The original eight local profiles supply actual 12273 moment certificates. -/
namespace BstLean.Part264b.N12273
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12273 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053423373513 ∧
    0 ≤ bN 12273 BstLean.Part154.csC (groupTheta g) ∧ bN 12273 BstLean.Part154.csC (groupTheta g) ≤ 0.001430422334 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12273 12273 0.011
      (momentAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12273 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12273 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12273 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231134968175 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12273 0.011
      (momentAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12273 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12273
/-! The actual computed-centre upper energy formula at 12273. -/
namespace BstLean.Part264b.N12273
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12273

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12273
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12273 cell12273)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086850786967
  | 2 => 0.087821341312
  | 3 => 0.088794525852
  | 4 => 0.089772756989
  | 5 => 0.090758918237
  | 6 => 0.091756424291
  | 7 => 0.092769290204
  | 8 => 0.093802205533
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12273 12273 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12273 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12273

/-! Actual upper energy certificates on all 43 source endpoints at 12273. -/
namespace BstLean.Part264b.N12273
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12273 cell12273)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12273 (gMinus 12273) (1 - (cell12273 i).lower) ≤ 1 ∧
    energyUpper 12273 (gMinus 12273) (BstLean.Part211.gPlus 12273)
      (finiteEnergy 12273 12273 0.011) (1 - (cell12273 i).lower) ≤
      (cell12273 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12273) (by norm_num)
        (q := 1 - (cell12273 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12273,cell12273]) (by norm_num [scalarRow12273,cell12273])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12273,cell12273])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12273

/-! Source-cell containment and simple scalar guards at 12273. -/
namespace BstLean.Part264b.N12273
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12273 cell12273)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12273 ⟨10,by decide⟩).lower ∧ (cell12273 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12273 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12273 ⟨11,by decide⟩).lower ∧ (cell12273 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12273 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12273 ⟨12,by decide⟩).lower ∧ (cell12273 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12273 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12273 ⟨13,by decide⟩).lower ∧ (cell12273 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12273 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12273 ⟨14,by decide⟩).lower ∧ (cell12273 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12273 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12273 ⟨15,by decide⟩).lower ∧ (cell12273 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12273 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12273 ⟨16,by decide⟩).lower ∧ (cell12273 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12273 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12273 ⟨17,by decide⟩).lower ∧ (cell12273 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12273 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12273 ⟨18,by decide⟩).lower ∧ (cell12273 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12273 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12273 ⟨19,by decide⟩).lower ∧ (cell12273 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12273 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12273 ⟨20,by decide⟩).lower ∧ (cell12273 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12273 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12273 ⟨21,by decide⟩).lower ∧ (cell12273 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12273 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12273 ⟨22,by decide⟩).lower ∧ (cell12273 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12273 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12273 ⟨23,by decide⟩).lower ∧ (cell12273 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12273 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12273 ⟨24,by decide⟩).lower ∧ (cell12273 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12273 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12273 ⟨25,by decide⟩).lower ∧ (cell12273 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12273 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12273 ⟨26,by decide⟩).lower ∧ (cell12273 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12273 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12273 ⟨27,by decide⟩).lower ∧ (cell12273 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12273 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12273 ⟨28,by decide⟩).lower ∧ (cell12273 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12273 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12273 ⟨29,by decide⟩).lower ∧ (cell12273 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12273 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12273 ⟨30,by decide⟩).lower ∧ (cell12273 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12273 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12273 ⟨31,by decide⟩).lower ∧ (cell12273 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12273 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12273 ⟨32,by decide⟩).lower ∧ (cell12273 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12273 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12273 ⟨33,by decide⟩).lower ∧ (cell12273 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12273 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12273 ⟨34,by decide⟩).lower ∧ (cell12273 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12273 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12273 ⟨35,by decide⟩).lower ∧ (cell12273 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12273 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12273 ⟨36,by decide⟩).lower ∧ (cell12273 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12273 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12273 ⟨37,by decide⟩).lower ∧ (cell12273 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12273 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12273 ⟨38,by decide⟩).lower ∧ (cell12273 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12273 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12273 ⟨39,by decide⟩).lower ∧ (cell12273 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12273 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12273 ⟨40,by decide⟩).lower ∧ (cell12273 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12273 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12273 ⟨41,by decide⟩).lower ∧ (cell12273 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12273 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12273 ⟨42,by decide⟩).lower ∧ (cell12273 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12273 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12273 ⟨43,by decide⟩).lower ∧ (cell12273 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12273 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12273 ⟨44,by decide⟩).lower ∧ (cell12273 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12273 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12273 ⟨45,by decide⟩).lower ∧ (cell12273 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12273 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12273 ⟨46,by decide⟩).lower ∧ (cell12273 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12273 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12273 ⟨47,by decide⟩).lower ∧ (cell12273 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12273 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12273 ⟨48,by decide⟩).lower ∧ (cell12273 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12273 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12273 ⟨49,by decide⟩).lower ∧ (cell12273 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12273 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12273 ⟨50,by decide⟩).lower ∧ (cell12273 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12273 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12273 ⟨51,by decide⟩).lower ∧ (cell12273 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12273 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12273 ⟨52,by decide⟩).lower ∧ (cell12273 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12273 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12273 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12273 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12273,cell12273,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12273 i).lower ∧
    (cell12273 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12273 i).upper ≤ (0.532 : ℝ) ∧
    (cell12273 i).centre ≤ (0.1 : ℝ) ∧ (cell12273 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12273 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12273 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12273

/-! The local source numeric instances at 12273 have no network premises. -/
namespace BstLean.Part264b.N12273
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12273 cell12273)

noncomputable def sourceNumerics12273 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12273 (cell12273 i)
      scalarRow12273.M scalarRow12273.H scalarRow12273.xi := by
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
    energy_allowance := scalarRow12273.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12273]
    centre_nonneg := (scalarRow12273.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12273]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12273
/-! Actual 12274 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12274
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12274 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12274 12274 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12274.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12274 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12274 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12274 := gPlus_lower 12274
end BstLean.Part264b.N12274

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12274
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036430857422 : ℝ) ≤ wn 12274 := by
  have hn : √(12274 : ℝ) ≤ 110.788086002061 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12274 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.788086002061 ≤ 2 / √12274 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260779439 : ℝ) ≤ rhoBar 12274 BstLean.Part154.csC ∧
    rhoBar 12274 BstLean.Part154.csC ≤ 0.000260798498 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036430857422 : ℝ) / (1.295212 * 12274) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12274) := by gcongr
      _ ≤ (0.000260798498 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12274 BstLean.Part154.csC) ≤ 0.001043262008 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12274 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12274 BstLean.Part154.csC) (piBar (rhoBar 12274 BstLean.Part154.csC)) ≤ 0.000199199980 ∧
    cc1 (rhoBar 12274 BstLean.Part154.csC) (piBar (rhoBar 12274 BstLean.Part154.csC)) ≤ 0.000126752203 ∧
    cc2 (rhoBar 12274 BstLean.Part154.csC) ≤ 0.000073580543 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12274 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12274 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12274 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12274 BstLean.Part154.csC * nuR (rhoBar 12274 BstLean.Part154.csC)) ≤ 0.000521614000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260798498 : ℝ) * 0.001043262008 := by gcongr
      _ ≤ (0.000521614000 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12274 BstLean.Part154.csC) * nuR (rhoBar 12274 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043262008 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12274 BstLean.Part154.csC) * rhoBar 12274 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260798498 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260798498 / 2 + 0.399 * 0.001043262008 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199199980 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521614000 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126752203 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260798498 / 1.414213562 := by gcongr
      _ ≤ (0.000073580543 : ℝ) := by norm_num

end BstLean.Part264b.N12274

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12274
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12274 BstLean.Part154.csC) (piBar (rhoBar 12274 BstLean.Part154.csC)) ≤ 1.71362E-7 := by
  have hr0 : 0 ≤ rhoBar 12274 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12274 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12274 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12274 BstLean.Part154.csC) (piBar (rhoBar 12274 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12274 BstLean.Part154.csC) (piBar (rhoBar 12274 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12274 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199199980 : ℝ) ^ 2 + 0.000126752203 ^ 2 + 3 * 0.000073580543 ^ 2 +
        2 * 0.797885 * 0.000199199980 * 0.000126752203 + 2 * 0.000199199980 * 0.000073580543 +
        4 * 0.797885 * 0.000126752203 * 0.000073580543 := by gcongr
    _ ≤ (1.71362E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12274 BstLean.Part154.csC Θ ≤ 0.002724410644 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12274 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12274 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12274 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12274 BstLean.Part154.csC) (piBar (rhoBar 12274 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12274 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71362E-7 / (0.000260779439 : ℝ) := by gcongr
    _ ≤ 0.002724410644 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12274 BstLean.Part154.csC Θ ≤ 0.003024685375 + 0.000688361690 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12274 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12274 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12274 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260798498 +
        (6863 / 10000) * 0.000260798498 * 12274 * 0.001043262008) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003024685375 + 0.000688361690 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12274 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12274 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12274 0.011 Θ ∧ gammaRatio 12274 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12274 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12274) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12274 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12274 0.011 Θ) :=
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
    badAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12274 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12274 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12274 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12274 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12274 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12274 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12274 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12274 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12274 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12274 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12274 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004124685375 + 0.003412772334 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12274

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12274
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12274 BstLean.Part154.csC) (piBar (rhoBar 12274 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12274 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12274 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12274 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12274 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12274 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12274 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12274 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12274 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12274 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12274 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12274 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12274 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053397304555 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12274) ≤ 0.010779476604 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12274 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010779476604 + 2 * 0.737676 / 12274) := by gcongr
    _ ≤ (0.053397304555 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12274 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12274

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12274
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483634666 : ℝ) ≤ plow 12274 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12274) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422990851)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430315589) : eMP 12274 0.011 xi bn ≤ 0.001230655354 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12274 : ℝ) * (1 - 0.011))) ≤ 0.000608414690 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001430315589 / (12274 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608414690 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608414690 : ℝ) + 3.141593 * 0.053422990851 / (12274 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001230655354 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422990851)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430315589) : PiBarMP 12274 12 0.011 xi bn ≤ 0.164059463755 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12274 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037819513337 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.177066579211 : ℝ) ≤ √((12274 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.788086002060 : ℝ) ≤ √12274 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12274) ≤ 0.125757279195 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037819513337 + 0.053422990851 * 1.772454 / (2 * (110.177066579211 : ℝ))) * (1 + 0.001230655354) +
        8 / (12274 * 110.788086002060) + 0.125757279195 := by gcongr
    _ ≤ (0.164059463755 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422990851)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430315589) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284531444939) :
    parallelOracle 12274 0.011 xi bn cd ≤ 0.165087230937 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12274 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12274 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483634666 : ℝ) ≤ plow 12274 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.788086002060 : ℝ) ≤ √12274 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284531444939 : ℝ) / (2 * 0.560483634666 * 110.788086002060)) * 0.164059463755 +
        0.284531444939 ^ 2 / (2 * 0.560483634666 * 110.788086002060) := by gcongr
    _ ≤ (0.165087230937 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422990851) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430315589)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284531444939) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12274 12274 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483634666 : ℝ) ≤ plow 12274 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.788086002060 : ℝ) ≤ √12274 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12274 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12274 Θ 1.22 ≤ 0.011969703132 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.788086002060 := by gcongr <;> linarith
      _ ≤ (0.011969703132 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12274 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12274 12274 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12274 12274 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12274 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12274 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12274 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12274 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165087230937 + 0.011969703132 + (0.008646 : ℝ) *
        (1 + 2 * (0.284531444939 + 0.011969703132) / (0.560483634666 * 110.788086002060))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12274]

end BstLean.Part264b.N12274

/-! The original eight local profiles supply actual 12274 moment certificates. -/
namespace BstLean.Part264b.N12274
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12274 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053422990851 ∧
    0 ≤ bN 12274 BstLean.Part154.csC (groupTheta g) ∧ bN 12274 BstLean.Part154.csC (groupTheta g) ≤ 0.001430315589 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12274 12274 0.011
      (momentAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12274 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12274 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12274 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231134140384 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12274 0.011
      (momentAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12274 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12274
/-! The actual computed-centre upper energy formula at 12274. -/
namespace BstLean.Part264b.N12274
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12274

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12274
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12274 cell12274)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086847287256
  | 2 => 0.087817762622
  | 3 => 0.088790854439
  | 4 => 0.089768976144
  | 5 => 0.090755007790
  | 6 => 0.091752360075
  | 7 => 0.092765043451
  | 8 => 0.093797742215
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12274 12274 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12274 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12274

/-! Actual upper energy certificates on all 43 source endpoints at 12274. -/
namespace BstLean.Part264b.N12274
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12274 cell12274)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12274 (gMinus 12274) (1 - (cell12274 i).lower) ≤ 1 ∧
    energyUpper 12274 (gMinus 12274) (BstLean.Part211.gPlus 12274)
      (finiteEnergy 12274 12274 0.011) (1 - (cell12274 i).lower) ≤
      (cell12274 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12274) (by norm_num)
        (q := 1 - (cell12274 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12274,cell12274]) (by norm_num [scalarRow12274,cell12274])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12274,cell12274])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12274

/-! Source-cell containment and simple scalar guards at 12274. -/
namespace BstLean.Part264b.N12274
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12274 cell12274)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12274 ⟨10,by decide⟩).lower ∧ (cell12274 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12274 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12274 ⟨11,by decide⟩).lower ∧ (cell12274 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12274 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12274 ⟨12,by decide⟩).lower ∧ (cell12274 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12274 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12274 ⟨13,by decide⟩).lower ∧ (cell12274 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12274 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12274 ⟨14,by decide⟩).lower ∧ (cell12274 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12274 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12274 ⟨15,by decide⟩).lower ∧ (cell12274 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12274 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12274 ⟨16,by decide⟩).lower ∧ (cell12274 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12274 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12274 ⟨17,by decide⟩).lower ∧ (cell12274 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12274 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12274 ⟨18,by decide⟩).lower ∧ (cell12274 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12274 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12274 ⟨19,by decide⟩).lower ∧ (cell12274 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12274 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12274 ⟨20,by decide⟩).lower ∧ (cell12274 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12274 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12274 ⟨21,by decide⟩).lower ∧ (cell12274 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12274 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12274 ⟨22,by decide⟩).lower ∧ (cell12274 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12274 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12274 ⟨23,by decide⟩).lower ∧ (cell12274 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12274 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12274 ⟨24,by decide⟩).lower ∧ (cell12274 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12274 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12274 ⟨25,by decide⟩).lower ∧ (cell12274 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12274 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12274 ⟨26,by decide⟩).lower ∧ (cell12274 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12274 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12274 ⟨27,by decide⟩).lower ∧ (cell12274 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12274 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12274 ⟨28,by decide⟩).lower ∧ (cell12274 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12274 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12274 ⟨29,by decide⟩).lower ∧ (cell12274 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12274 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12274 ⟨30,by decide⟩).lower ∧ (cell12274 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12274 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12274 ⟨31,by decide⟩).lower ∧ (cell12274 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12274 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12274 ⟨32,by decide⟩).lower ∧ (cell12274 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12274 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12274 ⟨33,by decide⟩).lower ∧ (cell12274 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12274 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12274 ⟨34,by decide⟩).lower ∧ (cell12274 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12274 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12274 ⟨35,by decide⟩).lower ∧ (cell12274 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12274 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12274 ⟨36,by decide⟩).lower ∧ (cell12274 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12274 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12274 ⟨37,by decide⟩).lower ∧ (cell12274 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12274 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12274 ⟨38,by decide⟩).lower ∧ (cell12274 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12274 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12274 ⟨39,by decide⟩).lower ∧ (cell12274 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12274 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12274 ⟨40,by decide⟩).lower ∧ (cell12274 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12274 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12274 ⟨41,by decide⟩).lower ∧ (cell12274 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12274 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12274 ⟨42,by decide⟩).lower ∧ (cell12274 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12274 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12274 ⟨43,by decide⟩).lower ∧ (cell12274 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12274 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12274 ⟨44,by decide⟩).lower ∧ (cell12274 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12274 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12274 ⟨45,by decide⟩).lower ∧ (cell12274 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12274 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12274 ⟨46,by decide⟩).lower ∧ (cell12274 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12274 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12274 ⟨47,by decide⟩).lower ∧ (cell12274 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12274 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12274 ⟨48,by decide⟩).lower ∧ (cell12274 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12274 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12274 ⟨49,by decide⟩).lower ∧ (cell12274 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12274 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12274 ⟨50,by decide⟩).lower ∧ (cell12274 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12274 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12274 ⟨51,by decide⟩).lower ∧ (cell12274 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12274 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12274 ⟨52,by decide⟩).lower ∧ (cell12274 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12274 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12274 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12274 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12274,cell12274,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12274 i).lower ∧
    (cell12274 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12274 i).upper ≤ (0.532 : ℝ) ∧
    (cell12274 i).centre ≤ (0.1 : ℝ) ∧ (cell12274 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12274 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12274 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12274

/-! The local source numeric instances at 12274 have no network premises. -/
namespace BstLean.Part264b.N12274
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12274 cell12274)

noncomputable def sourceNumerics12274 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12274 (cell12274 i)
      scalarRow12274.M scalarRow12274.H scalarRow12274.xi := by
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
    energy_allowance := scalarRow12274.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12274]
    centre_nonneg := (scalarRow12274.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12274]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12274
