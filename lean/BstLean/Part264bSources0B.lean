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
namespace BstLean.Part264b.N12239
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12239 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12239 12239 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12239.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12239 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12239 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12239 := gPlus_lower 12239
end BstLean.Part264b.N12239

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12239
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036483377403 : ℝ) ≤ wn 12239 := by
  have hn : √(12239 : ℝ) ≤ 110.630014010666 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12239 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.630014010666 ≤ 2 / √12239 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261538445 : ℝ) ≤ rhoBar 12239 BstLean.Part154.csC ∧
    rhoBar 12239 BstLean.Part154.csC ≤ 0.000261544306 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036483377403 : ℝ) / (1.295212 * 12239) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12239) := by gcongr
      _ ≤ (0.000261544306 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12239 BstLean.Part154.csC) ≤ 0.001046245630 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12239 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12239 BstLean.Part154.csC) (piBar (rhoBar 12239 BstLean.Part154.csC)) ≤ 0.000199769662 ∧
    cc1 (rhoBar 12239 BstLean.Part154.csC) (piBar (rhoBar 12239 BstLean.Part154.csC)) ≤ 0.000127114689 ∧
    cc2 (rhoBar 12239 BstLean.Part154.csC) ≤ 0.000073790962 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12239 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12239 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12239 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12239 BstLean.Part154.csC * nuR (rhoBar 12239 BstLean.Part154.csC)) ≤ 0.000523105714 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261544306 : ℝ) * 0.001046245630 := by gcongr
      _ ≤ (0.000523105714 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12239 BstLean.Part154.csC) * nuR (rhoBar 12239 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046245630 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12239 BstLean.Part154.csC) * rhoBar 12239 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261544306 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261544306 / 2 + 0.399 * 0.001046245630 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199769662 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523105714 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127114689 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261544306 / 1.414213562 := by gcongr
      _ ≤ (0.000073790962 : ℝ) := by norm_num

end BstLean.Part264b.N12239

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12239
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12239 BstLean.Part154.csC) (piBar (rhoBar 12239 BstLean.Part154.csC)) ≤ 1.72343E-7 := by
  have hr0 : 0 ≤ rhoBar 12239 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12239 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12239 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12239 BstLean.Part154.csC) (piBar (rhoBar 12239 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12239 BstLean.Part154.csC) (piBar (rhoBar 12239 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12239 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199769662 : ℝ) ^ 2 + 0.000127114689 ^ 2 + 3 * 0.000073790962 ^ 2 +
        2 * 0.797885 * 0.000199769662 * 0.000127114689 + 2 * 0.000199769662 * 0.000073790962 +
        4 * 0.797885 * 0.000127114689 * 0.000073790962 := by gcongr
    _ ≤ (1.72343E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12239 BstLean.Part154.csC Θ ≤ 0.002732055415 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12239 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12239 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12239 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12239 BstLean.Part154.csC) (piBar (rhoBar 12239 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12239 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72343E-7 / (0.000261538445 : ℝ) := by gcongr
    _ ≤ 0.002732055415 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12239 BstLean.Part154.csC Θ ≤ 0.003033335660 + 0.000690330205 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12239 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12239 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12239 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261544306 +
        (6863 / 10000) * 0.000261544306 * 12239 * 0.001046245630) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003033335660 + 0.000690330205 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12239 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12239 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12239 0.011 Θ ∧ gammaRatio 12239 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12239 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12239) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12239 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12239 0.011 Θ) :=
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
    badAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12239 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12239 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12239 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12239 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12239 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12239 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12239 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12239 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12239 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12239 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12239 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004133335660 + 0.003422385620 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12239

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12239
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12239 BstLean.Part154.csC) (piBar (rhoBar 12239 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12239 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12239 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12239 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12239 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12239 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12239 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12239 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12239 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12239 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12239 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12239 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12239 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053474443067 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12239) ≤ 0.010794878694 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12239 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010794878694 + 2 * 0.737676 / 12239) := by gcongr
    _ ≤ (0.053474443067 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12239 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12239

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12239
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481935239 : ℝ) ≤ plow 12239 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12239) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053436688111)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434329093) : eMP 12239 0.011 xi bn ≤ 0.001234145565 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12239 : ℝ) * (1 - 0.011))) ≤ 0.000610138249 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001434329093 / (12239 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610138249 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610138249 : ℝ) + 3.141593 * 0.053436688111 / (12239 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001234145565 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053436688111)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434329093) : PiBarMP 12239 12 0.011 xi bn ≤ 0.164293123634 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12239 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037872537452 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.019866387848 : ℝ) ≤ √((12239 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.630014010665 : ℝ) ≤ √12239 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12239) ≤ 0.125936965546 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037872537452 + 0.053436688111 * 1.772454 / (2 * (110.019866387848 : ℝ))) * (1 + 0.001234145565) +
        8 / (12239 * 110.630014010665) + 0.125936965546 := by gcongr
    _ ≤ (0.164293123634 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053436688111)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434329093) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284638212095) :
    parallelOracle 12239 0.011 xi bn cd ≤ 0.165323530019 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12239 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12239 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481935239 : ℝ) ≤ plow 12239 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.630014010665 : ℝ) ≤ √12239 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284638212095 : ℝ) / (2 * 0.560481935239 * 110.630014010665)) * 0.164293123634 +
        0.284638212095 ^ 2 / (2 * 0.560481935239 * 110.630014010665) := by gcongr
    _ ≤ (0.165323530019 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053436688111) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434329093)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284638212095) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12239 12239 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481935239 : ℝ) ≤ plow 12239 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.630014010665 : ℝ) ≤ √12239 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12239 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12239 Θ 1.22 ≤ 0.011986805858 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.630014010665 := by gcongr <;> linarith
      _ ≤ (0.011986805858 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12239 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12239 12239 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12239 12239 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12239 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12239 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12239 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12239 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165323530019 + 0.011986805858 + (0.008646 : ℝ) *
        (1 + 2 * (0.284638212095 + 0.011986805858) / (0.560481935239 * 110.630014010665))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12239]

end BstLean.Part264b.N12239

/-! The original eight local profiles supply actual 12239 moment certificates. -/
namespace BstLean.Part264b.N12239
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12239 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053436688111 ∧
    0 ≤ bN 12239 BstLean.Part154.csC (groupTheta g) ∧ bN 12239 BstLean.Part154.csC (groupTheta g) ≤ 0.001434329093 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12239 12239 0.011
      (momentAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12239 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12239 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12239 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231163769028 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12239 0.011
      (momentAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12239 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12239
/-! The actual computed-centre upper energy formula at 12239. -/
namespace BstLean.Part264b.N12239
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12239

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12239
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12239 cell12239)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086970807527
  | 2 => 0.087944094167
  | 3 => 0.088920489139
  | 4 => 0.089902511822
  | 5 => 0.090893165631
  | 6 => 0.091896003968
  | 7 => 0.092915201327
  | 8 => 0.093955629433
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12239 12239 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12239 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12239

/-! Actual upper energy certificates on all 43 source endpoints at 12239. -/
namespace BstLean.Part264b.N12239
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12239 cell12239)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12239 (gMinus 12239) (1 - (cell12239 i).lower) ≤ 1 ∧
    energyUpper 12239 (gMinus 12239) (BstLean.Part211.gPlus 12239)
      (finiteEnergy 12239 12239 0.011) (1 - (cell12239 i).lower) ≤
      (cell12239 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12239) (by norm_num)
        (q := 1 - (cell12239 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12239,cell12239]) (by norm_num [scalarRow12239,cell12239])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12239,cell12239])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12239

/-! Source-cell containment and simple scalar guards at 12239. -/
namespace BstLean.Part264b.N12239
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12239 cell12239)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12239 ⟨10,by decide⟩).lower ∧ (cell12239 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12239 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12239 ⟨11,by decide⟩).lower ∧ (cell12239 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12239 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12239 ⟨12,by decide⟩).lower ∧ (cell12239 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12239 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12239 ⟨13,by decide⟩).lower ∧ (cell12239 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12239 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12239 ⟨14,by decide⟩).lower ∧ (cell12239 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12239 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12239 ⟨15,by decide⟩).lower ∧ (cell12239 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12239 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12239 ⟨16,by decide⟩).lower ∧ (cell12239 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12239 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12239 ⟨17,by decide⟩).lower ∧ (cell12239 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12239 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12239 ⟨18,by decide⟩).lower ∧ (cell12239 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12239 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12239 ⟨19,by decide⟩).lower ∧ (cell12239 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12239 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12239 ⟨20,by decide⟩).lower ∧ (cell12239 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12239 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12239 ⟨21,by decide⟩).lower ∧ (cell12239 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12239 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12239 ⟨22,by decide⟩).lower ∧ (cell12239 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12239 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12239 ⟨23,by decide⟩).lower ∧ (cell12239 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12239 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12239 ⟨24,by decide⟩).lower ∧ (cell12239 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12239 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12239 ⟨25,by decide⟩).lower ∧ (cell12239 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12239 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12239 ⟨26,by decide⟩).lower ∧ (cell12239 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12239 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12239 ⟨27,by decide⟩).lower ∧ (cell12239 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12239 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12239 ⟨28,by decide⟩).lower ∧ (cell12239 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12239 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12239 ⟨29,by decide⟩).lower ∧ (cell12239 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12239 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12239 ⟨30,by decide⟩).lower ∧ (cell12239 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12239 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12239 ⟨31,by decide⟩).lower ∧ (cell12239 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12239 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12239 ⟨32,by decide⟩).lower ∧ (cell12239 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12239 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12239 ⟨33,by decide⟩).lower ∧ (cell12239 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12239 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12239 ⟨34,by decide⟩).lower ∧ (cell12239 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12239 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12239 ⟨35,by decide⟩).lower ∧ (cell12239 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12239 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12239 ⟨36,by decide⟩).lower ∧ (cell12239 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12239 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12239 ⟨37,by decide⟩).lower ∧ (cell12239 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12239 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12239 ⟨38,by decide⟩).lower ∧ (cell12239 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12239 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12239 ⟨39,by decide⟩).lower ∧ (cell12239 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12239 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12239 ⟨40,by decide⟩).lower ∧ (cell12239 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12239 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12239 ⟨41,by decide⟩).lower ∧ (cell12239 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12239 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12239 ⟨42,by decide⟩).lower ∧ (cell12239 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12239 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12239 ⟨43,by decide⟩).lower ∧ (cell12239 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12239 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12239 ⟨44,by decide⟩).lower ∧ (cell12239 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12239 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12239 ⟨45,by decide⟩).lower ∧ (cell12239 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12239 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12239 ⟨46,by decide⟩).lower ∧ (cell12239 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12239 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12239 ⟨47,by decide⟩).lower ∧ (cell12239 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12239 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12239 ⟨48,by decide⟩).lower ∧ (cell12239 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12239 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12239 ⟨49,by decide⟩).lower ∧ (cell12239 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12239 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12239 ⟨50,by decide⟩).lower ∧ (cell12239 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12239 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12239 ⟨51,by decide⟩).lower ∧ (cell12239 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12239 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12239 ⟨52,by decide⟩).lower ∧ (cell12239 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12239 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12239 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12239 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12239,cell12239,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12239 i).lower ∧
    (cell12239 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12239 i).upper ≤ (0.532 : ℝ) ∧
    (cell12239 i).centre ≤ (0.1 : ℝ) ∧ (cell12239 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12239 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12239 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12239

/-! The local source numeric instances at 12239 have no network premises. -/
namespace BstLean.Part264b.N12239
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12239 cell12239)

noncomputable def sourceNumerics12239 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12239 (cell12239 i)
      scalarRow12239.M scalarRow12239.H scalarRow12239.xi := by
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
    energy_allowance := scalarRow12239.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12239]
    centre_nonneg := (scalarRow12239.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12239]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12239
/-! Actual 12240 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12240
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12240 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12240 12240 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12240.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12240 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12240 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12240 := gPlus_lower 12240
end BstLean.Part264b.N12240

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12240
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036481873688 : ℝ) ≤ wn 12240 := by
  have hn : √(12240 : ℝ) ≤ 110.634533487515 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12240 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.634533487515 ≤ 2 / √12240 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261516698 : ℝ) ≤ rhoBar 12240 BstLean.Part154.csC ∧
    rhoBar 12240 BstLean.Part154.csC ≤ 0.000261522938 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036481873688 : ℝ) / (1.295212 * 12240) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12240) := by gcongr
      _ ≤ (0.000261522938 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12240 BstLean.Part154.csC) ≤ 0.001046160147 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12240 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12240 BstLean.Part154.csC) (piBar (rhoBar 12240 BstLean.Part154.csC)) ≤ 0.000199753340 ∧
    cc1 (rhoBar 12240 BstLean.Part154.csC) (piBar (rhoBar 12240 BstLean.Part154.csC)) ≤ 0.000127104303 ∧
    cc2 (rhoBar 12240 BstLean.Part154.csC) ≤ 0.000073784933 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12240 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12240 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12240 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12240 BstLean.Part154.csC * nuR (rhoBar 12240 BstLean.Part154.csC)) ≤ 0.000523062975 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261522938 : ℝ) * 0.001046160147 := by gcongr
      _ ≤ (0.000523062975 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12240 BstLean.Part154.csC) * nuR (rhoBar 12240 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046160147 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12240 BstLean.Part154.csC) * rhoBar 12240 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261522938 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261522938 / 2 + 0.399 * 0.001046160147 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199753340 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523062975 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127104303 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261522938 / 1.414213562 := by gcongr
      _ ≤ (0.000073784933 : ℝ) := by norm_num

end BstLean.Part264b.N12240

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12240
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12240 BstLean.Part154.csC) (piBar (rhoBar 12240 BstLean.Part154.csC)) ≤ 1.72315E-7 := by
  have hr0 : 0 ≤ rhoBar 12240 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12240 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12240 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12240 BstLean.Part154.csC) (piBar (rhoBar 12240 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12240 BstLean.Part154.csC) (piBar (rhoBar 12240 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12240 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199753340 : ℝ) ^ 2 + 0.000127104303 ^ 2 + 3 * 0.000073784933 ^ 2 +
        2 * 0.797885 * 0.000199753340 * 0.000127104303 + 2 * 0.000199753340 * 0.000073784933 +
        4 * 0.797885 * 0.000127104303 * 0.000073784933 := by gcongr
    _ ≤ (1.72315E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12240 BstLean.Part154.csC Θ ≤ 0.002731838701 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12240 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12240 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12240 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12240 BstLean.Part154.csC) (piBar (rhoBar 12240 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12240 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72315E-7 / (0.000261516698 : ℝ) := by gcongr
    _ ≤ 0.002731838701 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12240 BstLean.Part154.csC Θ ≤ 0.003033087823 + 0.000690273805 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12240 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12240 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12240 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261522938 +
        (6863 / 10000) * 0.000261522938 * 12240 * 0.001046160147) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003033087823 + 0.000690273805 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12240 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12240 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12240 0.011 Θ ∧ gammaRatio 12240 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12240 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12240) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12240 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12240 0.011 Θ) :=
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
    badAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12240 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12240 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12240 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12240 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12240 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12240 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12240 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12240 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12240 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12240 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12240 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004133087823 + 0.003422112506 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12240

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12240
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12240 BstLean.Part154.csC) (piBar (rhoBar 12240 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12240 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12240 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12240 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12240 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12240 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12240 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12240 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12240 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12240 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12240 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12240 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12240 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053472234483 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12240) ≤ 0.010794437717 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12240 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010794437717 + 2 * 0.737676 / 12240) := by gcongr
    _ ≤ (0.053472234483 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12240 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12240

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12240
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481983929 : ℝ) ≤ plow 12240 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12240) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053436296889)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434215319) : eMP 12240 0.011 xi bn ≤ 0.001234046084 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12240 : ℝ) * (1 - 0.011))) ≤ 0.000610089126 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001434215319 / (12240 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610089126 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610089126 : ℝ) + 3.141593 * 0.053436296889 / (12240 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001234046084 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053436296889)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434215319) : PiBarMP 12240 12 0.011 xi bn ≤ 0.164286449801 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12240 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037871035357 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.024360938839 : ℝ) ≤ √((12240 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.634533487514 : ℝ) ≤ √12240 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12240) ≤ 0.125931820957 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037871035357 + 0.053436296889 * 1.772454 / (2 * (110.024360938839 : ℝ))) * (1 + 0.001234046084) +
        8 / (12240 * 110.634533487514) + 0.125931820957 := by gcongr
    _ ≤ (0.164286449801 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053436296889)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434215319) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284635157309) :
    parallelOracle 12240 0.011 xi bn cd ≤ 0.165316780617 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12240 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12240 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481983929 : ℝ) ≤ plow 12240 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.634533487514 : ℝ) ≤ √12240 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284635157309 : ℝ) / (2 * 0.560481983929 * 110.634533487514)) * 0.164286449801 +
        0.284635157309 ^ 2 / (2 * 0.560481983929 * 110.634533487514) := by gcongr
    _ ≤ (0.165316780617 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053436296889) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434215319)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284635157309) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12240 12240 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481983929 : ℝ) ≤ plow 12240 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.634533487514 : ℝ) ≤ √12240 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12240 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12240 Θ 1.22 ≤ 0.011986316191 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.634533487514 := by gcongr <;> linarith
      _ ≤ (0.011986316191 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12240 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12240 12240 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12240 12240 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12240 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12240 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12240 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12240 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165316780617 + 0.011986316191 + (0.008646 : ℝ) *
        (1 + 2 * (0.284635157309 + 0.011986316191) / (0.560481983929 * 110.634533487514))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12240]

end BstLean.Part264b.N12240

/-! The original eight local profiles supply actual 12240 moment certificates. -/
namespace BstLean.Part264b.N12240
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12240 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053436296889 ∧
    0 ≤ bN 12240 BstLean.Part154.csC (groupTheta g) ∧ bN 12240 BstLean.Part154.csC (groupTheta g) ≤ 0.001434215319 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12240 12240 0.011
      (momentAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12240 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12240 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12240 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231162922826 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12240 0.011
      (momentAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12240 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12240
/-! The actual computed-centre upper energy formula at 12240. -/
namespace BstLean.Part264b.N12240
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12240

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12240
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12240 cell12240)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086967248571
  | 2 => 0.087940453527
  | 3 => 0.088916752445
  | 4 => 0.089898661618
  | 5 => 0.090889180870
  | 6 => 0.091891859446
  | 7 => 0.092910867065
  | 8 => 0.093951070001
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12240 12240 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12240 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12240

/-! Actual upper energy certificates on all 43 source endpoints at 12240. -/
namespace BstLean.Part264b.N12240
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12240 cell12240)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12240 (gMinus 12240) (1 - (cell12240 i).lower) ≤ 1 ∧
    energyUpper 12240 (gMinus 12240) (BstLean.Part211.gPlus 12240)
      (finiteEnergy 12240 12240 0.011) (1 - (cell12240 i).lower) ≤
      (cell12240 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12240) (by norm_num)
        (q := 1 - (cell12240 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12240,cell12240]) (by norm_num [scalarRow12240,cell12240])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12240,cell12240])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12240

/-! Source-cell containment and simple scalar guards at 12240. -/
namespace BstLean.Part264b.N12240
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12240 cell12240)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12240 ⟨10,by decide⟩).lower ∧ (cell12240 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12240 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12240 ⟨11,by decide⟩).lower ∧ (cell12240 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12240 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12240 ⟨12,by decide⟩).lower ∧ (cell12240 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12240 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12240 ⟨13,by decide⟩).lower ∧ (cell12240 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12240 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12240 ⟨14,by decide⟩).lower ∧ (cell12240 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12240 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12240 ⟨15,by decide⟩).lower ∧ (cell12240 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12240 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12240 ⟨16,by decide⟩).lower ∧ (cell12240 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12240 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12240 ⟨17,by decide⟩).lower ∧ (cell12240 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12240 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12240 ⟨18,by decide⟩).lower ∧ (cell12240 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12240 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12240 ⟨19,by decide⟩).lower ∧ (cell12240 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12240 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12240 ⟨20,by decide⟩).lower ∧ (cell12240 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12240 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12240 ⟨21,by decide⟩).lower ∧ (cell12240 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12240 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12240 ⟨22,by decide⟩).lower ∧ (cell12240 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12240 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12240 ⟨23,by decide⟩).lower ∧ (cell12240 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12240 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12240 ⟨24,by decide⟩).lower ∧ (cell12240 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12240 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12240 ⟨25,by decide⟩).lower ∧ (cell12240 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12240 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12240 ⟨26,by decide⟩).lower ∧ (cell12240 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12240 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12240 ⟨27,by decide⟩).lower ∧ (cell12240 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12240 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12240 ⟨28,by decide⟩).lower ∧ (cell12240 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12240 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12240 ⟨29,by decide⟩).lower ∧ (cell12240 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12240 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12240 ⟨30,by decide⟩).lower ∧ (cell12240 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12240 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12240 ⟨31,by decide⟩).lower ∧ (cell12240 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12240 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12240 ⟨32,by decide⟩).lower ∧ (cell12240 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12240 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12240 ⟨33,by decide⟩).lower ∧ (cell12240 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12240 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12240 ⟨34,by decide⟩).lower ∧ (cell12240 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12240 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12240 ⟨35,by decide⟩).lower ∧ (cell12240 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12240 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12240 ⟨36,by decide⟩).lower ∧ (cell12240 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12240 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12240 ⟨37,by decide⟩).lower ∧ (cell12240 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12240 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12240 ⟨38,by decide⟩).lower ∧ (cell12240 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12240 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12240 ⟨39,by decide⟩).lower ∧ (cell12240 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12240 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12240 ⟨40,by decide⟩).lower ∧ (cell12240 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12240 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12240 ⟨41,by decide⟩).lower ∧ (cell12240 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12240 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12240 ⟨42,by decide⟩).lower ∧ (cell12240 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12240 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12240 ⟨43,by decide⟩).lower ∧ (cell12240 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12240 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12240 ⟨44,by decide⟩).lower ∧ (cell12240 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12240 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12240 ⟨45,by decide⟩).lower ∧ (cell12240 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12240 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12240 ⟨46,by decide⟩).lower ∧ (cell12240 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12240 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12240 ⟨47,by decide⟩).lower ∧ (cell12240 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12240 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12240 ⟨48,by decide⟩).lower ∧ (cell12240 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12240 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12240 ⟨49,by decide⟩).lower ∧ (cell12240 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12240 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12240 ⟨50,by decide⟩).lower ∧ (cell12240 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12240 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12240 ⟨51,by decide⟩).lower ∧ (cell12240 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12240 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12240 ⟨52,by decide⟩).lower ∧ (cell12240 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12240 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12240 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12240 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12240,cell12240,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12240 i).lower ∧
    (cell12240 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12240 i).upper ≤ (0.532 : ℝ) ∧
    (cell12240 i).centre ≤ (0.1 : ℝ) ∧ (cell12240 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12240 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12240 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12240

/-! The local source numeric instances at 12240 have no network premises. -/
namespace BstLean.Part264b.N12240
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12240 cell12240)

noncomputable def sourceNumerics12240 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12240 (cell12240 i)
      scalarRow12240.M scalarRow12240.H scalarRow12240.xi := by
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
    energy_allowance := scalarRow12240.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12240]
    centre_nonneg := (scalarRow12240.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12240]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12240
/-! Actual 12241 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12241
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12241 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12241 12241 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12241.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12241 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12241 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12241 := gPlus_lower 12241
end BstLean.Part264b.N12241

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12241
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036480370159 : ℝ) ≤ wn 12241 := by
  have hn : √(12241 : ℝ) ≤ 110.639052779749 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12241 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.639052779749 ≤ 2 / √12241 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261494955 : ℝ) ≤ rhoBar 12241 BstLean.Part154.csC ∧
    rhoBar 12241 BstLean.Part154.csC ≤ 0.000261501574 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036480370159 : ℝ) / (1.295212 * 12241) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12241) := by gcongr
      _ ≤ (0.000261501574 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12241 BstLean.Part154.csC) ≤ 0.001046074680 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12241 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12241 BstLean.Part154.csC) (piBar (rhoBar 12241 BstLean.Part154.csC)) ≤ 0.000199737021 ∧
    cc1 (rhoBar 12241 BstLean.Part154.csC) (piBar (rhoBar 12241 BstLean.Part154.csC)) ≤ 0.000127093920 ∧
    cc2 (rhoBar 12241 BstLean.Part154.csC) ≤ 0.000073778905 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12241 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12241 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12241 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12241 BstLean.Part154.csC * nuR (rhoBar 12241 BstLean.Part154.csC)) ≤ 0.000523020244 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261501574 : ℝ) * 0.001046074680 := by gcongr
      _ ≤ (0.000523020244 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12241 BstLean.Part154.csC) * nuR (rhoBar 12241 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001046074680 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12241 BstLean.Part154.csC) * rhoBar 12241 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261501574 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261501574 / 2 + 0.399 * 0.001046074680 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199737021 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523020244 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127093920 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261501574 / 1.414213562 := by gcongr
      _ ≤ (0.000073778905 : ℝ) := by norm_num

end BstLean.Part264b.N12241

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12241
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12241 BstLean.Part154.csC) (piBar (rhoBar 12241 BstLean.Part154.csC)) ≤ 1.72287E-7 := by
  have hr0 : 0 ≤ rhoBar 12241 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12241 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12241 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12241 BstLean.Part154.csC) (piBar (rhoBar 12241 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12241 BstLean.Part154.csC) (piBar (rhoBar 12241 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12241 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199737021 : ℝ) ^ 2 + 0.000127093920 ^ 2 + 3 * 0.000073778905 ^ 2 +
        2 * 0.797885 * 0.000199737021 * 0.000127093920 + 2 * 0.000199737021 * 0.000073778905 +
        4 * 0.797885 * 0.000127093920 * 0.000073778905 := by gcongr
    _ ≤ (1.72287E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12241 BstLean.Part154.csC Θ ≤ 0.002731621908 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12241 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12241 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12241 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12241 BstLean.Part154.csC) (piBar (rhoBar 12241 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12241 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72287E-7 / (0.000261494955 : ℝ) := by gcongr
    _ ≤ 0.002731621908 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12241 BstLean.Part154.csC Θ ≤ 0.003032840038 + 0.000690217416 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12241 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12241 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12241 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261501574 +
        (6863 / 10000) * 0.000261501574 * 12241 * 0.001046074680) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003032840038 + 0.000690217416 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12241 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12241 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12241 0.011 Θ ∧ gammaRatio 12241 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12241 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12241) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12241 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12241 0.011 Θ) :=
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
    badAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12241 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12241 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12241 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12241 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12241 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12241 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12241 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12241 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12241 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12241 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12241 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004132840038 + 0.003421839324 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12241

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12241
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12241 BstLean.Part154.csC) (piBar (rhoBar 12241 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12241 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12241 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12241 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12241 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12241 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12241 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12241 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12241 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12241 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12241 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12241 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12241 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053470026175 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12241) ≤ 0.010793996795 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12241 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010793996795 + 2 * 0.737676 / 12241) := by gcongr
    _ ≤ (0.053470026175 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12241 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12241

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12241
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482032611 : ℝ) ≤ plow 12241 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12241) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435905684)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434101502) : eMP 12241 0.011 xi bn ≤ 0.001233946594 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12241 : ℝ) * (1 - 0.011))) ≤ 0.000610039998 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001434101502 / (12241 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610039998 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610039998 : ℝ) + 3.141593 * 0.053435905684 / (12241 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001233946594 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435905684)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434101502) : PiBarMP 12241 12 0.011 xi bn ≤ 0.164279775974 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12241 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037869532636 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.028855306233 : ℝ) ≤ √((12241 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.639052779748 : ℝ) ≤ √12241 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12241) ≤ 0.125926676998 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037869532636 + 0.053435905684 * 1.772454 / (2 * (110.028855306233 : ℝ))) * (1 + 0.001233946594) +
        8 / (12241 * 110.639052779748) + 0.125926676998 := by gcongr
    _ ≤ (0.164279775974 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435905684)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434101502) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284632102832) :
    parallelOracle 12241 0.011 xi bn cd ≤ 0.165310031232 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12241 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12241 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482032611 : ℝ) ≤ plow 12241 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.639052779748 : ℝ) ≤ √12241 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284632102832 : ℝ) / (2 * 0.560482032611 * 110.639052779748)) * 0.164279775974 +
        0.284632102832 ^ 2 / (2 * 0.560482032611 * 110.639052779748) := by gcongr
    _ ≤ (0.165310031232 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435905684) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001434101502)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284632102832) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12241 12241 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482032611 : ℝ) ≤ plow 12241 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.639052779748 : ℝ) ≤ √12241 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12241 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12241 Θ 1.22 ≤ 0.011985826584 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.639052779748 := by gcongr <;> linarith
      _ ≤ (0.011985826584 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12241 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12241 12241 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12241 12241 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12241 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12241 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12241 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12241 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165310031232 + 0.011985826584 + (0.008646 : ℝ) *
        (1 + 2 * (0.284632102832 + 0.011985826584) / (0.560482032611 * 110.639052779748))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12241]

end BstLean.Part264b.N12241

/-! The original eight local profiles supply actual 12241 moment certificates. -/
namespace BstLean.Part264b.N12241
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12241 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053435905684 ∧
    0 ≤ bN 12241 BstLean.Part154.csC (groupTheta g) ∧ bN 12241 BstLean.Part154.csC (groupTheta g) ≤ 0.001434101502 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12241 12241 0.011
      (momentAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12241 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12241 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12241 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231162076657 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12241 0.011
      (momentAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12241 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12241
/-! The actual computed-centre upper energy formula at 12241. -/
namespace BstLean.Part264b.N12241
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12241

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12241
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12241 cell12241)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086963691390
  | 2 => 0.087936814743
  | 3 => 0.088913017708
  | 4 => 0.089894813494
  | 5 => 0.090885198337
  | 6 => 0.091887717331
  | 7 => 0.092906535427
  | 8 => 0.093946513451
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12241 12241 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12241 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12241

/-! Actual upper energy certificates on all 43 source endpoints at 12241. -/
namespace BstLean.Part264b.N12241
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12241 cell12241)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12241 (gMinus 12241) (1 - (cell12241 i).lower) ≤ 1 ∧
    energyUpper 12241 (gMinus 12241) (BstLean.Part211.gPlus 12241)
      (finiteEnergy 12241 12241 0.011) (1 - (cell12241 i).lower) ≤
      (cell12241 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12241) (by norm_num)
        (q := 1 - (cell12241 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12241,cell12241]) (by norm_num [scalarRow12241,cell12241])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12241,cell12241])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12241

/-! Source-cell containment and simple scalar guards at 12241. -/
namespace BstLean.Part264b.N12241
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12241 cell12241)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12241 ⟨10,by decide⟩).lower ∧ (cell12241 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12241 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12241 ⟨11,by decide⟩).lower ∧ (cell12241 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12241 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12241 ⟨12,by decide⟩).lower ∧ (cell12241 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12241 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12241 ⟨13,by decide⟩).lower ∧ (cell12241 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12241 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12241 ⟨14,by decide⟩).lower ∧ (cell12241 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12241 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12241 ⟨15,by decide⟩).lower ∧ (cell12241 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12241 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12241 ⟨16,by decide⟩).lower ∧ (cell12241 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12241 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12241 ⟨17,by decide⟩).lower ∧ (cell12241 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12241 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12241 ⟨18,by decide⟩).lower ∧ (cell12241 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12241 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12241 ⟨19,by decide⟩).lower ∧ (cell12241 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12241 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12241 ⟨20,by decide⟩).lower ∧ (cell12241 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12241 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12241 ⟨21,by decide⟩).lower ∧ (cell12241 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12241 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12241 ⟨22,by decide⟩).lower ∧ (cell12241 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12241 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12241 ⟨23,by decide⟩).lower ∧ (cell12241 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12241 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12241 ⟨24,by decide⟩).lower ∧ (cell12241 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12241 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12241 ⟨25,by decide⟩).lower ∧ (cell12241 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12241 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12241 ⟨26,by decide⟩).lower ∧ (cell12241 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12241 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12241 ⟨27,by decide⟩).lower ∧ (cell12241 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12241 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12241 ⟨28,by decide⟩).lower ∧ (cell12241 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12241 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12241 ⟨29,by decide⟩).lower ∧ (cell12241 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12241 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12241 ⟨30,by decide⟩).lower ∧ (cell12241 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12241 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12241 ⟨31,by decide⟩).lower ∧ (cell12241 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12241 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12241 ⟨32,by decide⟩).lower ∧ (cell12241 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12241 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12241 ⟨33,by decide⟩).lower ∧ (cell12241 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12241 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12241 ⟨34,by decide⟩).lower ∧ (cell12241 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12241 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12241 ⟨35,by decide⟩).lower ∧ (cell12241 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12241 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12241 ⟨36,by decide⟩).lower ∧ (cell12241 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12241 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12241 ⟨37,by decide⟩).lower ∧ (cell12241 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12241 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12241 ⟨38,by decide⟩).lower ∧ (cell12241 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12241 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12241 ⟨39,by decide⟩).lower ∧ (cell12241 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12241 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12241 ⟨40,by decide⟩).lower ∧ (cell12241 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12241 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12241 ⟨41,by decide⟩).lower ∧ (cell12241 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12241 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12241 ⟨42,by decide⟩).lower ∧ (cell12241 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12241 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12241 ⟨43,by decide⟩).lower ∧ (cell12241 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12241 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12241 ⟨44,by decide⟩).lower ∧ (cell12241 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12241 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12241 ⟨45,by decide⟩).lower ∧ (cell12241 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12241 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12241 ⟨46,by decide⟩).lower ∧ (cell12241 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12241 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12241 ⟨47,by decide⟩).lower ∧ (cell12241 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12241 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12241 ⟨48,by decide⟩).lower ∧ (cell12241 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12241 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12241 ⟨49,by decide⟩).lower ∧ (cell12241 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12241 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12241 ⟨50,by decide⟩).lower ∧ (cell12241 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12241 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12241 ⟨51,by decide⟩).lower ∧ (cell12241 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12241 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12241 ⟨52,by decide⟩).lower ∧ (cell12241 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12241 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12241 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12241 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12241,cell12241,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12241 i).lower ∧
    (cell12241 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12241 i).upper ≤ (0.532 : ℝ) ∧
    (cell12241 i).centre ≤ (0.1 : ℝ) ∧ (cell12241 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12241 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12241 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12241

/-! The local source numeric instances at 12241 have no network premises. -/
namespace BstLean.Part264b.N12241
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12241 cell12241)

noncomputable def sourceNumerics12241 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12241 (cell12241 i)
      scalarRow12241.M scalarRow12241.H scalarRow12241.xi := by
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
    energy_allowance := scalarRow12241.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12241]
    centre_nonneg := (scalarRow12241.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12241]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12241
/-! Actual 12242 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12242
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12242 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12242 12242 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12242.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12242 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12242 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12242 := gPlus_lower 12242
end BstLean.Part264b.N12242

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12242
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036478866815 : ℝ) ≤ wn 12242 := by
  have hn : √(12242 : ℝ) ≤ 110.643571887390 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12242 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.643571887390 ≤ 2 / √12242 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261473215 : ℝ) ≤ rhoBar 12242 BstLean.Part154.csC ∧
    rhoBar 12242 BstLean.Part154.csC ≤ 0.000261480213 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036478866815 : ℝ) / (1.295212 * 12242) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12242) := by gcongr
      _ ≤ (0.000261480213 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12242 BstLean.Part154.csC) ≤ 0.001045989224 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12242 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12242 BstLean.Part154.csC) (piBar (rhoBar 12242 BstLean.Part154.csC)) ≤ 0.000199720705 ∧
    cc1 (rhoBar 12242 BstLean.Part154.csC) (piBar (rhoBar 12242 BstLean.Part154.csC)) ≤ 0.000127083538 ∧
    cc2 (rhoBar 12242 BstLean.Part154.csC) ≤ 0.000073772879 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12242 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12242 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12242 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12242 BstLean.Part154.csC * nuR (rhoBar 12242 BstLean.Part154.csC)) ≤ 0.000522977519 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261480213 : ℝ) * 0.001045989224 := by gcongr
      _ ≤ (0.000522977519 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12242 BstLean.Part154.csC) * nuR (rhoBar 12242 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045989224 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12242 BstLean.Part154.csC) * rhoBar 12242 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261480213 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261480213 / 2 + 0.399 * 0.001045989224 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199720705 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522977519 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127083538 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261480213 / 1.414213562 := by gcongr
      _ ≤ (0.000073772879 : ℝ) := by norm_num

end BstLean.Part264b.N12242

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12242
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12242 BstLean.Part154.csC) (piBar (rhoBar 12242 BstLean.Part154.csC)) ≤ 1.72259E-7 := by
  have hr0 : 0 ≤ rhoBar 12242 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12242 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12242 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12242 BstLean.Part154.csC) (piBar (rhoBar 12242 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12242 BstLean.Part154.csC) (piBar (rhoBar 12242 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12242 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199720705 : ℝ) ^ 2 + 0.000127083538 ^ 2 + 3 * 0.000073772879 ^ 2 +
        2 * 0.797885 * 0.000199720705 * 0.000127083538 + 2 * 0.000199720705 * 0.000073772879 +
        4 * 0.797885 * 0.000127083538 * 0.000073772879 := by gcongr
    _ ≤ (1.72259E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12242 BstLean.Part154.csC Θ ≤ 0.002731405048 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12242 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12242 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12242 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12242 BstLean.Part154.csC) (piBar (rhoBar 12242 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12242 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72259E-7 / (0.000261473215 : ℝ) := by gcongr
    _ ≤ 0.002731405048 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12242 BstLean.Part154.csC Θ ≤ 0.003032592279 + 0.000690161035 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12242 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12242 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12242 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261480213 +
        (6863 / 10000) * 0.000261480213 * 12242 * 0.001045989224) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003032592279 + 0.000690161035 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12242 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12242 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12242 0.011 Θ ∧ gammaRatio 12242 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12242 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12242) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12242 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12242 0.011 Θ) :=
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
    badAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12242 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12242 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12242 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12242 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12242 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12242 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12242 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12242 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12242 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12242 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12242 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004132592279 + 0.003421566083 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12242

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12242
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12242 BstLean.Part154.csC) (piBar (rhoBar 12242 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12242 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12242 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12242 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12242 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12242 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12242 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12242 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12242 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12242 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12242 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12242 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12242 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053467818140 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12242) ≤ 0.010793555927 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12242 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010793555927 + 2 * 0.737676 / 12242) := by gcongr
    _ ≤ (0.053467818140 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12242 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12242

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12242
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482081285 : ℝ) ≤ plow 12242 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12242) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435514473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433987651) : eMP 12242 0.011 xi bn ≤ 0.001233847098 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12242 : ℝ) * (1 - 0.011))) ≤ 0.000609990867 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001433987651 / (12242 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609990867 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609990867 : ℝ) + 3.141593 * 0.053435514473 / (12242 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001233847098 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435514473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433987651) : PiBarMP 12242 12 0.011 xi bn ≤ 0.164273102270 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12242 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037868029405 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.033349490052 : ℝ) ≤ √((12242 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.643571887389 : ℝ) ≤ √12242 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12242) ≤ 0.125921533670 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037868029405 + 0.053435514473 * 1.772454 / (2 * (110.033349490052 : ℝ))) * (1 + 0.001233847098) +
        8 / (12242 * 110.643571887389) + 0.125921533670 := by gcongr
    _ ≤ (0.164273102270 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435514473)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433987651) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284629048612) :
    parallelOracle 12242 0.011 xi bn cd ≤ 0.165303281979 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12242 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12242 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482081285 : ℝ) ≤ plow 12242 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.643571887389 : ℝ) ≤ √12242 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284629048612 : ℝ) / (2 * 0.560482081285 * 110.643571887389)) * 0.164273102270 +
        0.284629048612 ^ 2 / (2 * 0.560482081285 * 110.643571887389) := by gcongr
    _ ≤ (0.165303281979 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435514473) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433987651)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284629048612) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12242 12242 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482081285 : ℝ) ≤ plow 12242 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.643571887389 : ℝ) ≤ √12242 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12242 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12242 Θ 1.22 ≤ 0.011985337037 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.643571887389 := by gcongr <;> linarith
      _ ≤ (0.011985337037 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12242 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12242 12242 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12242 12242 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12242 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12242 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12242 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12242 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165303281979 + 0.011985337037 + (0.008646 : ℝ) *
        (1 + 2 * (0.284629048612 + 0.011985337037) / (0.560482081285 * 110.643571887389))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12242]

end BstLean.Part264b.N12242

/-! The original eight local profiles supply actual 12242 moment certificates. -/
namespace BstLean.Part264b.N12242
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12242 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053435514473 ∧
    0 ≤ bN 12242 BstLean.Part154.csC (groupTheta g) ∧ bN 12242 BstLean.Part154.csC (groupTheta g) ≤ 0.001433987651 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12242 12242 0.011
      (momentAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12242 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12242 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12242 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231161230472 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12242 0.011
      (momentAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12242 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12242
/-! The actual computed-centre upper energy formula at 12242. -/
namespace BstLean.Part264b.N12242
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12242

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12242
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12242 cell12242)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086960135983
  | 2 => 0.087933177813
  | 3 => 0.088909284924
  | 4 => 0.089890967447
  | 5 => 0.090881218029
  | 6 => 0.091883577621
  | 7 => 0.092902206410
  | 8 => 0.093941959780
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12242 12242 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12242 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12242

/-! Actual upper energy certificates on all 43 source endpoints at 12242. -/
namespace BstLean.Part264b.N12242
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12242 cell12242)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12242 (gMinus 12242) (1 - (cell12242 i).lower) ≤ 1 ∧
    energyUpper 12242 (gMinus 12242) (BstLean.Part211.gPlus 12242)
      (finiteEnergy 12242 12242 0.011) (1 - (cell12242 i).lower) ≤
      (cell12242 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12242) (by norm_num)
        (q := 1 - (cell12242 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12242,cell12242]) (by norm_num [scalarRow12242,cell12242])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12242,cell12242])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12242

/-! Source-cell containment and simple scalar guards at 12242. -/
namespace BstLean.Part264b.N12242
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12242 cell12242)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12242 ⟨10,by decide⟩).lower ∧ (cell12242 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12242 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12242 ⟨11,by decide⟩).lower ∧ (cell12242 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12242 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12242 ⟨12,by decide⟩).lower ∧ (cell12242 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12242 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12242 ⟨13,by decide⟩).lower ∧ (cell12242 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12242 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12242 ⟨14,by decide⟩).lower ∧ (cell12242 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12242 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12242 ⟨15,by decide⟩).lower ∧ (cell12242 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12242 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12242 ⟨16,by decide⟩).lower ∧ (cell12242 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12242 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12242 ⟨17,by decide⟩).lower ∧ (cell12242 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12242 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12242 ⟨18,by decide⟩).lower ∧ (cell12242 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12242 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12242 ⟨19,by decide⟩).lower ∧ (cell12242 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12242 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12242 ⟨20,by decide⟩).lower ∧ (cell12242 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12242 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12242 ⟨21,by decide⟩).lower ∧ (cell12242 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12242 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12242 ⟨22,by decide⟩).lower ∧ (cell12242 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12242 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12242 ⟨23,by decide⟩).lower ∧ (cell12242 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12242 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12242 ⟨24,by decide⟩).lower ∧ (cell12242 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12242 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12242 ⟨25,by decide⟩).lower ∧ (cell12242 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12242 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12242 ⟨26,by decide⟩).lower ∧ (cell12242 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12242 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12242 ⟨27,by decide⟩).lower ∧ (cell12242 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12242 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12242 ⟨28,by decide⟩).lower ∧ (cell12242 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12242 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12242 ⟨29,by decide⟩).lower ∧ (cell12242 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12242 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12242 ⟨30,by decide⟩).lower ∧ (cell12242 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12242 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12242 ⟨31,by decide⟩).lower ∧ (cell12242 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12242 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12242 ⟨32,by decide⟩).lower ∧ (cell12242 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12242 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12242 ⟨33,by decide⟩).lower ∧ (cell12242 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12242 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12242 ⟨34,by decide⟩).lower ∧ (cell12242 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12242 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12242 ⟨35,by decide⟩).lower ∧ (cell12242 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12242 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12242 ⟨36,by decide⟩).lower ∧ (cell12242 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12242 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12242 ⟨37,by decide⟩).lower ∧ (cell12242 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12242 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12242 ⟨38,by decide⟩).lower ∧ (cell12242 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12242 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12242 ⟨39,by decide⟩).lower ∧ (cell12242 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12242 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12242 ⟨40,by decide⟩).lower ∧ (cell12242 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12242 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12242 ⟨41,by decide⟩).lower ∧ (cell12242 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12242 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12242 ⟨42,by decide⟩).lower ∧ (cell12242 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12242 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12242 ⟨43,by decide⟩).lower ∧ (cell12242 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12242 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12242 ⟨44,by decide⟩).lower ∧ (cell12242 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12242 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12242 ⟨45,by decide⟩).lower ∧ (cell12242 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12242 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12242 ⟨46,by decide⟩).lower ∧ (cell12242 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12242 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12242 ⟨47,by decide⟩).lower ∧ (cell12242 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12242 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12242 ⟨48,by decide⟩).lower ∧ (cell12242 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12242 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12242 ⟨49,by decide⟩).lower ∧ (cell12242 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12242 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12242 ⟨50,by decide⟩).lower ∧ (cell12242 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12242 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12242 ⟨51,by decide⟩).lower ∧ (cell12242 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12242 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12242 ⟨52,by decide⟩).lower ∧ (cell12242 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12242 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12242 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12242 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12242,cell12242,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12242 i).lower ∧
    (cell12242 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12242 i).upper ≤ (0.532 : ℝ) ∧
    (cell12242 i).centre ≤ (0.1 : ℝ) ∧ (cell12242 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12242 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12242 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12242

/-! The local source numeric instances at 12242 have no network premises. -/
namespace BstLean.Part264b.N12242
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12242 cell12242)

noncomputable def sourceNumerics12242 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12242 (cell12242 i)
      scalarRow12242.M scalarRow12242.H scalarRow12242.xi := by
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
    energy_allowance := scalarRow12242.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12242]
    centre_nonneg := (scalarRow12242.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12242]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12242
/-! Actual 12243 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12243
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12243 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12243 12243 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12243.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12243 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12243 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12243 := gPlus_lower 12243
end BstLean.Part264b.N12243

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12243
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036477363656 : ℝ) ≤ wn 12243 := by
  have hn : √(12243 : ℝ) ≤ 110.648090810461 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12243 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.648090810461 ≤ 2 / √12243 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261451479 : ℝ) ≤ rhoBar 12243 BstLean.Part154.csC ∧
    rhoBar 12243 BstLean.Part154.csC ≤ 0.000261458855 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036477363656 : ℝ) / (1.295212 * 12243) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12243) := by gcongr
      _ ≤ (0.000261458855 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12243 BstLean.Part154.csC) ≤ 0.001045903781 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12243 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12243 BstLean.Part154.csC) (piBar (rhoBar 12243 BstLean.Part154.csC)) ≤ 0.000199704390 ∧
    cc1 (rhoBar 12243 BstLean.Part154.csC) (piBar (rhoBar 12243 BstLean.Part154.csC)) ≤ 0.000127073157 ∧
    cc2 (rhoBar 12243 BstLean.Part154.csC) ≤ 0.000073766853 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12243 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12243 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12243 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12243 BstLean.Part154.csC * nuR (rhoBar 12243 BstLean.Part154.csC)) ≤ 0.000522934800 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261458855 : ℝ) * 0.001045903781 := by gcongr
      _ ≤ (0.000522934800 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12243 BstLean.Part154.csC) * nuR (rhoBar 12243 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045903781 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12243 BstLean.Part154.csC) * rhoBar 12243 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261458855 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261458855 / 2 + 0.399 * 0.001045903781 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199704390 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522934800 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127073157 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261458855 / 1.414213562 := by gcongr
      _ ≤ (0.000073766853 : ℝ) := by norm_num

end BstLean.Part264b.N12243

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12243
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12243 BstLean.Part154.csC) (piBar (rhoBar 12243 BstLean.Part154.csC)) ≤ 1.72230E-7 := by
  have hr0 : 0 ≤ rhoBar 12243 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12243 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12243 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12243 BstLean.Part154.csC) (piBar (rhoBar 12243 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12243 BstLean.Part154.csC) (piBar (rhoBar 12243 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12243 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199704390 : ℝ) ^ 2 + 0.000127073157 ^ 2 + 3 * 0.000073766853 ^ 2 +
        2 * 0.797885 * 0.000199704390 * 0.000127073157 + 2 * 0.000199704390 * 0.000073766853 +
        4 * 0.797885 * 0.000127073157 * 0.000073766853 := by gcongr
    _ ≤ (1.72230E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12243 BstLean.Part154.csC Θ ≤ 0.002731172252 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12243 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12243 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12243 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12243 BstLean.Part154.csC) (piBar (rhoBar 12243 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12243 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72230E-7 / (0.000261451479 : ℝ) := by gcongr
    _ ≤ 0.002731172252 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12243 BstLean.Part154.csC Θ ≤ 0.003032344553 + 0.000690104662 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12243 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12243 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12243 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261458855 +
        (6863 / 10000) * 0.000261458855 * 12243 * 0.001045903781) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003032344553 + 0.000690104662 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12243 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12243 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12243 0.011 Θ ∧ gammaRatio 12243 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12243 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12243) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12243 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12243 0.011 Θ) :=
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
    badAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12243 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12243 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12243 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12243 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12243 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12243 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12243 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12243 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12243 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12243 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12243 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004132344553 + 0.003421276914 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12243

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12243
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12243 BstLean.Part154.csC) (piBar (rhoBar 12243 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12243 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12243 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12243 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12243 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12243 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12243 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12243 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12243 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12243 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12243 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12243 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12243 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053465610377 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12243) ≤ 0.010793115113 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12243 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010793115113 + 2 * 0.737676 / 12243) := by gcongr
    _ ≤ (0.053465610377 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12243 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12243

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12243
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482129951 : ℝ) ≤ plow 12243 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12243) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435114933)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433865433) : eMP 12243 0.011 xi bn ≤ 0.001233744049 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12243 : ℝ) * (1 - 0.011))) ≤ 0.000609939961 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001433865433 / (12243 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609939961 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609939961 : ℝ) + 3.141593 * 0.053435114933 / (12243 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001233744049 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435114933)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433865433) : PiBarMP 12243 12 0.011 xi bn ≤ 0.164266318321 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12243 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037866415635 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.037843490319 : ℝ) ≤ √((12243 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.648090810460 : ℝ) ≤ √12243 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12243) ≤ 0.125916390972 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037866415635 + 0.053435114933 * 1.772454 / (2 * (110.037843490319 : ℝ))) * (1 + 0.001233744049) +
        8 / (12243 * 110.648090810460) + 0.125916390972 := by gcongr
    _ ≤ (0.164266318321 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435114933)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433865433) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284625976645) :
    parallelOracle 12243 0.011 xi bn cd ≤ 0.165296422133 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12243 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12243 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482129951 : ℝ) ≤ plow 12243 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.648090810460 : ℝ) ≤ √12243 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284625976645 : ℝ) / (2 * 0.560482129951 * 110.648090810460)) * 0.164266318321 +
        0.284625976645 ^ 2 / (2 * 0.560482129951 * 110.648090810460) := by gcongr
    _ ≤ (0.165296422133 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053435114933) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433865433)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284625976645) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12243 12243 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482129951 : ℝ) ≤ plow 12243 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.648090810460 : ℝ) ≤ √12243 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12243 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12243 Θ 1.22 ≤ 0.011984847550 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.648090810460 := by gcongr <;> linarith
      _ ≤ (0.011984847550 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12243 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12243 12243 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12243 12243 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12243 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12243 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12243 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12243 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165296422133 + 0.011984847550 + (0.008646 : ℝ) *
        (1 + 2 * (0.284625976645 + 0.011984847550) / (0.560482129951 * 110.648090810460))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12243]

end BstLean.Part264b.N12243

/-! The original eight local profiles supply actual 12243 moment certificates. -/
namespace BstLean.Part264b.N12243
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12243 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053435114933 ∧
    0 ≤ bN 12243 BstLean.Part154.csC (groupTheta g) ∧ bN 12243 BstLean.Part154.csC (groupTheta g) ≤ 0.001433865433 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12243 12243 0.011
      (momentAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12243 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12243 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12243 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231160366268 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12243 0.011
      (momentAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12243 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12243
/-! The actual computed-centre upper energy formula at 12243. -/
namespace BstLean.Part264b.N12243
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12243

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12243
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12243 cell12243)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086956582346
  | 2 => 0.087929542735
  | 3 => 0.088905554093
  | 4 => 0.089887123473
  | 5 => 0.090877239943
  | 6 => 0.091879440313
  | 7 => 0.092897880011
  | 8 => 0.093937408985
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12243 12243 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12243 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12243

/-! Actual upper energy certificates on all 43 source endpoints at 12243. -/
namespace BstLean.Part264b.N12243
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12243 cell12243)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12243 (gMinus 12243) (1 - (cell12243 i).lower) ≤ 1 ∧
    energyUpper 12243 (gMinus 12243) (BstLean.Part211.gPlus 12243)
      (finiteEnergy 12243 12243 0.011) (1 - (cell12243 i).lower) ≤
      (cell12243 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12243) (by norm_num)
        (q := 1 - (cell12243 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12243,cell12243]) (by norm_num [scalarRow12243,cell12243])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12243,cell12243])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12243

/-! Source-cell containment and simple scalar guards at 12243. -/
namespace BstLean.Part264b.N12243
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12243 cell12243)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12243 ⟨10,by decide⟩).lower ∧ (cell12243 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12243 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12243 ⟨11,by decide⟩).lower ∧ (cell12243 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12243 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12243 ⟨12,by decide⟩).lower ∧ (cell12243 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12243 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12243 ⟨13,by decide⟩).lower ∧ (cell12243 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12243 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12243 ⟨14,by decide⟩).lower ∧ (cell12243 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12243 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12243 ⟨15,by decide⟩).lower ∧ (cell12243 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12243 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12243 ⟨16,by decide⟩).lower ∧ (cell12243 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12243 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12243 ⟨17,by decide⟩).lower ∧ (cell12243 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12243 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12243 ⟨18,by decide⟩).lower ∧ (cell12243 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12243 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12243 ⟨19,by decide⟩).lower ∧ (cell12243 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12243 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12243 ⟨20,by decide⟩).lower ∧ (cell12243 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12243 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12243 ⟨21,by decide⟩).lower ∧ (cell12243 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12243 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12243 ⟨22,by decide⟩).lower ∧ (cell12243 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12243 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12243 ⟨23,by decide⟩).lower ∧ (cell12243 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12243 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12243 ⟨24,by decide⟩).lower ∧ (cell12243 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12243 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12243 ⟨25,by decide⟩).lower ∧ (cell12243 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12243 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12243 ⟨26,by decide⟩).lower ∧ (cell12243 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12243 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12243 ⟨27,by decide⟩).lower ∧ (cell12243 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12243 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12243 ⟨28,by decide⟩).lower ∧ (cell12243 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12243 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12243 ⟨29,by decide⟩).lower ∧ (cell12243 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12243 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12243 ⟨30,by decide⟩).lower ∧ (cell12243 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12243 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12243 ⟨31,by decide⟩).lower ∧ (cell12243 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12243 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12243 ⟨32,by decide⟩).lower ∧ (cell12243 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12243 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12243 ⟨33,by decide⟩).lower ∧ (cell12243 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12243 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12243 ⟨34,by decide⟩).lower ∧ (cell12243 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12243 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12243 ⟨35,by decide⟩).lower ∧ (cell12243 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12243 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12243 ⟨36,by decide⟩).lower ∧ (cell12243 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12243 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12243 ⟨37,by decide⟩).lower ∧ (cell12243 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12243 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12243 ⟨38,by decide⟩).lower ∧ (cell12243 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12243 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12243 ⟨39,by decide⟩).lower ∧ (cell12243 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12243 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12243 ⟨40,by decide⟩).lower ∧ (cell12243 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12243 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12243 ⟨41,by decide⟩).lower ∧ (cell12243 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12243 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12243 ⟨42,by decide⟩).lower ∧ (cell12243 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12243 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12243 ⟨43,by decide⟩).lower ∧ (cell12243 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12243 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12243 ⟨44,by decide⟩).lower ∧ (cell12243 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12243 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12243 ⟨45,by decide⟩).lower ∧ (cell12243 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12243 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12243 ⟨46,by decide⟩).lower ∧ (cell12243 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12243 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12243 ⟨47,by decide⟩).lower ∧ (cell12243 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12243 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12243 ⟨48,by decide⟩).lower ∧ (cell12243 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12243 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12243 ⟨49,by decide⟩).lower ∧ (cell12243 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12243 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12243 ⟨50,by decide⟩).lower ∧ (cell12243 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12243 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12243 ⟨51,by decide⟩).lower ∧ (cell12243 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12243 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12243 ⟨52,by decide⟩).lower ∧ (cell12243 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12243 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12243 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12243 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12243,cell12243,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12243 i).lower ∧
    (cell12243 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12243 i).upper ≤ (0.532 : ℝ) ∧
    (cell12243 i).centre ≤ (0.1 : ℝ) ∧ (cell12243 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12243 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12243 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12243

/-! The local source numeric instances at 12243 have no network premises. -/
namespace BstLean.Part264b.N12243
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12243 cell12243)

noncomputable def sourceNumerics12243 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12243 (cell12243 i)
      scalarRow12243.M scalarRow12243.H scalarRow12243.xi := by
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
    energy_allowance := scalarRow12243.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12243]
    centre_nonneg := (scalarRow12243.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12243]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12243
/-! Actual 12244 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12244
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12244 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12244 12244 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12244.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12244 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12244 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12244 := gPlus_lower 12244
end BstLean.Part264b.N12244

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12244
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036475860682 : ℝ) ≤ wn 12244 := by
  have hn : √(12244 : ℝ) ≤ 110.652609548985 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12244 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.652609548985 ≤ 2 / √12244 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261429747 : ℝ) ≤ rhoBar 12244 BstLean.Part154.csC ∧
    rhoBar 12244 BstLean.Part154.csC ≤ 0.000261437501 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036475860682 : ℝ) / (1.295212 * 12244) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12244) := by gcongr
      _ ≤ (0.000261437501 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12244 BstLean.Part154.csC) ≤ 0.001045818354 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12244 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12244 BstLean.Part154.csC) (piBar (rhoBar 12244 BstLean.Part154.csC)) ≤ 0.000199688079 ∧
    cc1 (rhoBar 12244 BstLean.Part154.csC) (piBar (rhoBar 12244 BstLean.Part154.csC)) ≤ 0.000127062778 ∧
    cc2 (rhoBar 12244 BstLean.Part154.csC) ≤ 0.000073760828 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12244 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12244 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12244 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12244 BstLean.Part154.csC * nuR (rhoBar 12244 BstLean.Part154.csC)) ≤ 0.000522892090 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261437501 : ℝ) * 0.001045818354 := by gcongr
      _ ≤ (0.000522892090 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12244 BstLean.Part154.csC) * nuR (rhoBar 12244 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045818354 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12244 BstLean.Part154.csC) * rhoBar 12244 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261437501 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261437501 / 2 + 0.399 * 0.001045818354 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199688079 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522892090 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127062778 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261437501 / 1.414213562 := by gcongr
      _ ≤ (0.000073760828 : ℝ) := by norm_num

end BstLean.Part264b.N12244

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12244
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12244 BstLean.Part154.csC) (piBar (rhoBar 12244 BstLean.Part154.csC)) ≤ 1.72202E-7 := by
  have hr0 : 0 ≤ rhoBar 12244 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12244 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12244 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12244 BstLean.Part154.csC) (piBar (rhoBar 12244 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12244 BstLean.Part154.csC) (piBar (rhoBar 12244 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12244 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199688079 : ℝ) ^ 2 + 0.000127062778 ^ 2 + 3 * 0.000073760828 ^ 2 +
        2 * 0.797885 * 0.000199688079 * 0.000127062778 + 2 * 0.000199688079 * 0.000073760828 +
        4 * 0.797885 * 0.000127062778 * 0.000073760828 := by gcongr
    _ ≤ (1.72202E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12244 BstLean.Part154.csC Θ ≤ 0.002730955235 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12244 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12244 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12244 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12244 BstLean.Part154.csC) (piBar (rhoBar 12244 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12244 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72202E-7 / (0.000261429747 : ℝ) := by gcongr
    _ ≤ 0.002730955235 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12244 BstLean.Part154.csC Θ ≤ 0.003032096878 + 0.000690048300 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12244 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12244 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12244 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261437501 +
        (6863 / 10000) * 0.000261437501 * 12244 * 0.001045818354) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003032096878 + 0.000690048300 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12244 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12244 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12244 0.011 Θ ∧ gammaRatio 12244 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12244 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12244) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12244 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12244 0.011 Θ) :=
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
    badAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12244 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12244 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12244 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12244 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12244 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12244 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12244 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12244 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12244 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12244 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12244 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004132096878 + 0.003421003535 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12244

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12244
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12244 BstLean.Part154.csC) (piBar (rhoBar 12244 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12244 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12244 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12244 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12244 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12244 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12244 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12244 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12244 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12244 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12244 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12244 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12244 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053463402882 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12244) ≤ 0.010792674352 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12244 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010792674352 + 2 * 0.737676 / 12244) := by gcongr
    _ ≤ (0.053463402882 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12244 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12244

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12244
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482178609 : ℝ) ≤ plow 12244 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12244) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053434723734)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433751499) : eMP 12244 0.011 xi bn ≤ 0.001233644536 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12244 : ℝ) * (1 - 0.011))) ≤ 0.000609890821 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001433751499 / (12244 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609890821 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609890821 : ℝ) + 3.141593 * 0.053434723734 / (12244 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001233644536 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053434723734)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433751499) : PiBarMP 12244 12 0.011 xi bn ≤ 0.164259644662 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12244 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037864911185 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.042337307056 : ℝ) ≤ √((12244 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.652609548984 : ℝ) ≤ √12244 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12244) ≤ 0.125911248904 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037864911185 + 0.053434723734 * 1.772454 / (2 * (110.042337307056 : ℝ))) * (1 + 0.001233644536) +
        8 / (12244 * 110.652609548984) + 0.125911248904 := by gcongr
    _ ≤ (0.164259644662 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053434723734)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433751499) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284622922985) :
    parallelOracle 12244 0.011 xi bn cd ≤ 0.165289672946 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12244 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12244 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482178609 : ℝ) ≤ plow 12244 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.652609548984 : ℝ) ≤ √12244 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284622922985 : ℝ) / (2 * 0.560482178609 * 110.652609548984)) * 0.164259644662 +
        0.284622922985 ^ 2 / (2 * 0.560482178609 * 110.652609548984) := by gcongr
    _ ≤ (0.165289672946 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053434723734) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433751499)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284622922985) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12244 12244 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482178609 : ℝ) ≤ plow 12244 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.652609548984 : ℝ) ≤ √12244 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12244 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12244 Θ 1.22 ≤ 0.011984358123 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.652609548984 := by gcongr <;> linarith
      _ ≤ (0.011984358123 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12244 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12244 12244 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12244 12244 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12244 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12244 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12244 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12244 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165289672946 + 0.011984358123 + (0.008646 : ℝ) *
        (1 + 2 * (0.284622922985 + 0.011984358123) / (0.560482178609 * 110.652609548984))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12244]

end BstLean.Part264b.N12244

/-! The original eight local profiles supply actual 12244 moment certificates. -/
namespace BstLean.Part264b.N12244
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12244 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053434723734 ∧
    0 ≤ bN 12244 BstLean.Part154.csC (groupTheta g) ∧ bN 12244 BstLean.Part154.csC (groupTheta g) ≤ 0.001433751499 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12244 12244 0.011
      (momentAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12244 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12244 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12244 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231159520103 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12244 0.011
      (momentAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12244 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12244
/-! The actual computed-centre upper energy formula at 12244. -/
namespace BstLean.Part264b.N12244
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12244

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12244
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12244 cell12244)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086953030478
  | 2 => 0.087925909507
  | 3 => 0.088901825211
  | 4 => 0.089883281571
  | 5 => 0.090873264078
  | 6 => 0.091875305405
  | 7 => 0.092893556226
  | 8 => 0.093932861061
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12244 12244 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12244 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12244

/-! Actual upper energy certificates on all 43 source endpoints at 12244. -/
namespace BstLean.Part264b.N12244
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12244 cell12244)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12244 (gMinus 12244) (1 - (cell12244 i).lower) ≤ 1 ∧
    energyUpper 12244 (gMinus 12244) (BstLean.Part211.gPlus 12244)
      (finiteEnergy 12244 12244 0.011) (1 - (cell12244 i).lower) ≤
      (cell12244 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12244) (by norm_num)
        (q := 1 - (cell12244 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12244,cell12244]) (by norm_num [scalarRow12244,cell12244])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12244,cell12244])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12244

/-! Source-cell containment and simple scalar guards at 12244. -/
namespace BstLean.Part264b.N12244
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12244 cell12244)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12244 ⟨10,by decide⟩).lower ∧ (cell12244 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12244 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12244 ⟨11,by decide⟩).lower ∧ (cell12244 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12244 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12244 ⟨12,by decide⟩).lower ∧ (cell12244 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12244 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12244 ⟨13,by decide⟩).lower ∧ (cell12244 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12244 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12244 ⟨14,by decide⟩).lower ∧ (cell12244 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12244 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12244 ⟨15,by decide⟩).lower ∧ (cell12244 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12244 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12244 ⟨16,by decide⟩).lower ∧ (cell12244 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12244 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12244 ⟨17,by decide⟩).lower ∧ (cell12244 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12244 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12244 ⟨18,by decide⟩).lower ∧ (cell12244 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12244 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12244 ⟨19,by decide⟩).lower ∧ (cell12244 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12244 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12244 ⟨20,by decide⟩).lower ∧ (cell12244 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12244 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12244 ⟨21,by decide⟩).lower ∧ (cell12244 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12244 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12244 ⟨22,by decide⟩).lower ∧ (cell12244 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12244 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12244 ⟨23,by decide⟩).lower ∧ (cell12244 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12244 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12244 ⟨24,by decide⟩).lower ∧ (cell12244 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12244 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12244 ⟨25,by decide⟩).lower ∧ (cell12244 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12244 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12244 ⟨26,by decide⟩).lower ∧ (cell12244 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12244 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12244 ⟨27,by decide⟩).lower ∧ (cell12244 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12244 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12244 ⟨28,by decide⟩).lower ∧ (cell12244 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12244 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12244 ⟨29,by decide⟩).lower ∧ (cell12244 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12244 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12244 ⟨30,by decide⟩).lower ∧ (cell12244 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12244 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12244 ⟨31,by decide⟩).lower ∧ (cell12244 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12244 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12244 ⟨32,by decide⟩).lower ∧ (cell12244 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12244 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12244 ⟨33,by decide⟩).lower ∧ (cell12244 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12244 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12244 ⟨34,by decide⟩).lower ∧ (cell12244 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12244 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12244 ⟨35,by decide⟩).lower ∧ (cell12244 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12244 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12244 ⟨36,by decide⟩).lower ∧ (cell12244 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12244 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12244 ⟨37,by decide⟩).lower ∧ (cell12244 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12244 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12244 ⟨38,by decide⟩).lower ∧ (cell12244 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12244 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12244 ⟨39,by decide⟩).lower ∧ (cell12244 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12244 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12244 ⟨40,by decide⟩).lower ∧ (cell12244 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12244 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12244 ⟨41,by decide⟩).lower ∧ (cell12244 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12244 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12244 ⟨42,by decide⟩).lower ∧ (cell12244 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12244 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12244 ⟨43,by decide⟩).lower ∧ (cell12244 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12244 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12244 ⟨44,by decide⟩).lower ∧ (cell12244 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12244 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12244 ⟨45,by decide⟩).lower ∧ (cell12244 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12244 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12244 ⟨46,by decide⟩).lower ∧ (cell12244 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12244 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12244 ⟨47,by decide⟩).lower ∧ (cell12244 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12244 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12244 ⟨48,by decide⟩).lower ∧ (cell12244 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12244 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12244 ⟨49,by decide⟩).lower ∧ (cell12244 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12244 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12244 ⟨50,by decide⟩).lower ∧ (cell12244 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12244 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12244 ⟨51,by decide⟩).lower ∧ (cell12244 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12244 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12244 ⟨52,by decide⟩).lower ∧ (cell12244 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12244 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12244 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12244 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12244,cell12244,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12244 i).lower ∧
    (cell12244 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12244 i).upper ≤ (0.532 : ℝ) ∧
    (cell12244 i).centre ≤ (0.1 : ℝ) ∧ (cell12244 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12244 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12244 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12244

/-! The local source numeric instances at 12244 have no network premises. -/
namespace BstLean.Part264b.N12244
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12244 cell12244)

noncomputable def sourceNumerics12244 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12244 (cell12244 i)
      scalarRow12244.M scalarRow12244.H scalarRow12244.xi := by
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
    energy_allowance := scalarRow12244.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12244]
    centre_nonneg := (scalarRow12244.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12244]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12244
/-! Actual 12245 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12245
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12245 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12245 12245 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12245.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12245 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12245 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12245 := gPlus_lower 12245
end BstLean.Part264b.N12245

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12245
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036474357893 : ℝ) ≤ wn 12245 := by
  have hn : √(12245 : ℝ) ≤ 110.657128102984 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12245 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.657128102984 ≤ 2 / √12245 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261408018 : ℝ) ≤ rhoBar 12245 BstLean.Part154.csC ∧
    rhoBar 12245 BstLean.Part154.csC ≤ 0.000261416151 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036474357893 : ℝ) / (1.295212 * 12245) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12245) := by gcongr
      _ ≤ (0.000261416151 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12245 BstLean.Part154.csC) ≤ 0.001045732943 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12245 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12245 BstLean.Part154.csC) (piBar (rhoBar 12245 BstLean.Part154.csC)) ≤ 0.000199671771 ∧
    cc1 (rhoBar 12245 BstLean.Part154.csC) (piBar (rhoBar 12245 BstLean.Part154.csC)) ≤ 0.000127052402 ∧
    cc2 (rhoBar 12245 BstLean.Part154.csC) ≤ 0.000073754805 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12245 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12245 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12245 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12245 BstLean.Part154.csC * nuR (rhoBar 12245 BstLean.Part154.csC)) ≤ 0.000522849387 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261416151 : ℝ) * 0.001045732943 := by gcongr
      _ ≤ (0.000522849387 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12245 BstLean.Part154.csC) * nuR (rhoBar 12245 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045732943 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12245 BstLean.Part154.csC) * rhoBar 12245 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261416151 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261416151 / 2 + 0.399 * 0.001045732943 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199671771 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522849387 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127052402 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261416151 / 1.414213562 := by gcongr
      _ ≤ (0.000073754805 : ℝ) := by norm_num

end BstLean.Part264b.N12245

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12245
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12245 BstLean.Part154.csC) (piBar (rhoBar 12245 BstLean.Part154.csC)) ≤ 1.72174E-7 := by
  have hr0 : 0 ≤ rhoBar 12245 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12245 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12245 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12245 BstLean.Part154.csC) (piBar (rhoBar 12245 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12245 BstLean.Part154.csC) (piBar (rhoBar 12245 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12245 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199671771 : ℝ) ^ 2 + 0.000127052402 ^ 2 + 3 * 0.000073754805 ^ 2 +
        2 * 0.797885 * 0.000199671771 * 0.000127052402 + 2 * 0.000199671771 * 0.000073754805 +
        4 * 0.797885 * 0.000127052402 * 0.000073754805 := by gcongr
    _ ≤ (1.72174E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12245 BstLean.Part154.csC Θ ≤ 0.002730738151 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12245 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12245 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12245 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12245 BstLean.Part154.csC) (piBar (rhoBar 12245 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12245 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72174E-7 / (0.000261408018 : ℝ) := by gcongr
    _ ≤ 0.002730738151 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12245 BstLean.Part154.csC Θ ≤ 0.003031849256 + 0.000689991947 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12245 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12245 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12245 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261416151 +
        (6863 / 10000) * 0.000261416151 * 12245 * 0.001045732943) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003031849256 + 0.000689991947 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12245 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12245 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12245 0.011 Θ ∧ gammaRatio 12245 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12245 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12245) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12245 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12245 0.011 Θ) :=
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
    badAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12245 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12245 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12245 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12245 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12245 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12245 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12245 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12245 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12245 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12245 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12245 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004131849256 + 0.003420730098 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12245

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12245
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12245 BstLean.Part154.csC) (piBar (rhoBar 12245 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12245 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12245 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12245 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12245 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12245 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12245 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12245 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12245 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12245 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12245 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12245 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12245 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053461195664 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12245) ≤ 0.010792233646 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12245 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010792233646 + 2 * 0.737676 / 12245) := by gcongr
    _ ≤ (0.053461195664 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12245 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12245

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12245
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482227260 : ℝ) ≤ plow 12245 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12245) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053434332558)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433637530) : eMP 12245 0.011 xi bn ≤ 0.001233545014 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12245 : ℝ) * (1 - 0.011))) ≤ 0.000609841677 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001433637530 / (12245 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609841677 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609841677 : ℝ) + 3.141593 * 0.053434332558 / (12245 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001233545014 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053434332558)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433637530) : PiBarMP 12245 12 0.011 xi bn ≤ 0.164252971113 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12245 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037863406213 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.046830940286 : ℝ) ≤ √((12245 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.657128102983 : ℝ) ≤ √12245 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12245) ≤ 0.125906107466 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037863406213 + 0.053434332558 * 1.772454 / (2 * (110.046830940286 : ℝ))) * (1 + 0.001233545014) +
        8 / (12245 * 110.657128102983) + 0.125906107466 := by gcongr
    _ ≤ (0.164252971113 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053434332558)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433637530) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284619869648) :
    parallelOracle 12245 0.011 xi bn cd ≤ 0.165282923879 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12245 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12245 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482227260 : ℝ) ≤ plow 12245 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.657128102983 : ℝ) ≤ √12245 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284619869648 : ℝ) / (2 * 0.560482227260 * 110.657128102983)) * 0.164252971113 +
        0.284619869648 ^ 2 / (2 * 0.560482227260 * 110.657128102983) := by gcongr
    _ ≤ (0.165282923879 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053434332558) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433637530)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284619869648) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12245 12245 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482227260 : ℝ) ≤ plow 12245 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.657128102983 : ℝ) ≤ √12245 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12245 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12245 Θ 1.22 ≤ 0.011983868756 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.657128102983 := by gcongr <;> linarith
      _ ≤ (0.011983868756 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12245 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12245 12245 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12245 12245 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12245 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12245 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12245 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12245 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165282923879 + 0.011983868756 + (0.008646 : ℝ) *
        (1 + 2 * (0.284619869648 + 0.011983868756) / (0.560482227260 * 110.657128102983))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12245]

end BstLean.Part264b.N12245

/-! The original eight local profiles supply actual 12245 moment certificates. -/
namespace BstLean.Part264b.N12245
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12245 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053434332558 ∧
    0 ≤ bN 12245 BstLean.Part154.csC (groupTheta g) ∧ bN 12245 BstLean.Part154.csC (groupTheta g) ≤ 0.001433637530 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12245 12245 0.011
      (momentAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12245 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12245 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12245 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231158673984 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12245 0.011
      (momentAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12245 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12245
/-! The actual computed-centre upper energy formula at 12245. -/
namespace BstLean.Part264b.N12245
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12245

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12245
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12245 cell12245)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086949480378
  | 2 => 0.087922278127
  | 3 => 0.088898098277
  | 4 => 0.089879441739
  | 5 => 0.090869290430
  | 6 => 0.091871172893
  | 7 => 0.092889235053
  | 8 => 0.093928316006
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12245 12245 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12245 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12245

/-! Actual upper energy certificates on all 43 source endpoints at 12245. -/
namespace BstLean.Part264b.N12245
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12245 cell12245)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12245 (gMinus 12245) (1 - (cell12245 i).lower) ≤ 1 ∧
    energyUpper 12245 (gMinus 12245) (BstLean.Part211.gPlus 12245)
      (finiteEnergy 12245 12245 0.011) (1 - (cell12245 i).lower) ≤
      (cell12245 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12245) (by norm_num)
        (q := 1 - (cell12245 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12245,cell12245]) (by norm_num [scalarRow12245,cell12245])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12245,cell12245])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12245

/-! Source-cell containment and simple scalar guards at 12245. -/
namespace BstLean.Part264b.N12245
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12245 cell12245)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12245 ⟨10,by decide⟩).lower ∧ (cell12245 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12245 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12245 ⟨11,by decide⟩).lower ∧ (cell12245 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12245 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12245 ⟨12,by decide⟩).lower ∧ (cell12245 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12245 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12245 ⟨13,by decide⟩).lower ∧ (cell12245 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12245 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12245 ⟨14,by decide⟩).lower ∧ (cell12245 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12245 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12245 ⟨15,by decide⟩).lower ∧ (cell12245 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12245 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12245 ⟨16,by decide⟩).lower ∧ (cell12245 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12245 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12245 ⟨17,by decide⟩).lower ∧ (cell12245 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12245 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12245 ⟨18,by decide⟩).lower ∧ (cell12245 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12245 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12245 ⟨19,by decide⟩).lower ∧ (cell12245 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12245 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12245 ⟨20,by decide⟩).lower ∧ (cell12245 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12245 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12245 ⟨21,by decide⟩).lower ∧ (cell12245 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12245 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12245 ⟨22,by decide⟩).lower ∧ (cell12245 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12245 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12245 ⟨23,by decide⟩).lower ∧ (cell12245 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12245 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12245 ⟨24,by decide⟩).lower ∧ (cell12245 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12245 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12245 ⟨25,by decide⟩).lower ∧ (cell12245 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12245 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12245 ⟨26,by decide⟩).lower ∧ (cell12245 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12245 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12245 ⟨27,by decide⟩).lower ∧ (cell12245 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12245 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12245 ⟨28,by decide⟩).lower ∧ (cell12245 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12245 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12245 ⟨29,by decide⟩).lower ∧ (cell12245 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12245 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12245 ⟨30,by decide⟩).lower ∧ (cell12245 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12245 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12245 ⟨31,by decide⟩).lower ∧ (cell12245 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12245 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12245 ⟨32,by decide⟩).lower ∧ (cell12245 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12245 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12245 ⟨33,by decide⟩).lower ∧ (cell12245 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12245 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12245 ⟨34,by decide⟩).lower ∧ (cell12245 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12245 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12245 ⟨35,by decide⟩).lower ∧ (cell12245 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12245 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12245 ⟨36,by decide⟩).lower ∧ (cell12245 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12245 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12245 ⟨37,by decide⟩).lower ∧ (cell12245 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12245 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12245 ⟨38,by decide⟩).lower ∧ (cell12245 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12245 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12245 ⟨39,by decide⟩).lower ∧ (cell12245 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12245 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12245 ⟨40,by decide⟩).lower ∧ (cell12245 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12245 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12245 ⟨41,by decide⟩).lower ∧ (cell12245 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12245 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12245 ⟨42,by decide⟩).lower ∧ (cell12245 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12245 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12245 ⟨43,by decide⟩).lower ∧ (cell12245 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12245 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12245 ⟨44,by decide⟩).lower ∧ (cell12245 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12245 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12245 ⟨45,by decide⟩).lower ∧ (cell12245 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12245 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12245 ⟨46,by decide⟩).lower ∧ (cell12245 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12245 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12245 ⟨47,by decide⟩).lower ∧ (cell12245 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12245 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12245 ⟨48,by decide⟩).lower ∧ (cell12245 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12245 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12245 ⟨49,by decide⟩).lower ∧ (cell12245 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12245 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12245 ⟨50,by decide⟩).lower ∧ (cell12245 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12245 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12245 ⟨51,by decide⟩).lower ∧ (cell12245 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12245 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12245 ⟨52,by decide⟩).lower ∧ (cell12245 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12245 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12245 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12245 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12245,cell12245,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12245 i).lower ∧
    (cell12245 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12245 i).upper ≤ (0.532 : ℝ) ∧
    (cell12245 i).centre ≤ (0.1 : ℝ) ∧ (cell12245 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12245 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12245 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12245

/-! The local source numeric instances at 12245 have no network premises. -/
namespace BstLean.Part264b.N12245
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12245 cell12245)

noncomputable def sourceNumerics12245 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12245 (cell12245 i)
      scalarRow12245.M scalarRow12245.H scalarRow12245.xi := by
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
    energy_allowance := scalarRow12245.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12245]
    centre_nonneg := (scalarRow12245.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12245]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12245
/-! Actual 12246 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12246
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12246 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12246 12246 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12246.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12246 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12246 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12246 := gPlus_lower 12246
end BstLean.Part264b.N12246

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12246
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036472855290 : ℝ) ≤ wn 12246 := by
  have hn : √(12246 : ℝ) ≤ 110.661646472480 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12246 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.661646472480 ≤ 2 / √12246 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261386292 : ℝ) ≤ rhoBar 12246 BstLean.Part154.csC ∧
    rhoBar 12246 BstLean.Part154.csC ≤ 0.000261394804 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036472855290 : ℝ) / (1.295212 * 12246) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12246) := by gcongr
      _ ≤ (0.000261394804 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12246 BstLean.Part154.csC) ≤ 0.001045647544 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12246 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12246 BstLean.Part154.csC) (piBar (rhoBar 12246 BstLean.Part154.csC)) ≤ 0.000199655466 ∧
    cc1 (rhoBar 12246 BstLean.Part154.csC) (piBar (rhoBar 12246 BstLean.Part154.csC)) ≤ 0.000127042026 ∧
    cc2 (rhoBar 12246 BstLean.Part154.csC) ≤ 0.000073748782 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12246 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12246 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12246 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12246 BstLean.Part154.csC * nuR (rhoBar 12246 BstLean.Part154.csC)) ≤ 0.000522806690 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261394804 : ℝ) * 0.001045647544 := by gcongr
      _ ≤ (0.000522806690 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12246 BstLean.Part154.csC) * nuR (rhoBar 12246 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045647544 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12246 BstLean.Part154.csC) * rhoBar 12246 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261394804 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261394804 / 2 + 0.399 * 0.001045647544 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199655466 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522806690 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127042026 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261394804 / 1.414213562 := by gcongr
      _ ≤ (0.000073748782 : ℝ) := by norm_num

end BstLean.Part264b.N12246

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12246
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12246 BstLean.Part154.csC) (piBar (rhoBar 12246 BstLean.Part154.csC)) ≤ 1.72146E-7 := by
  have hr0 : 0 ≤ rhoBar 12246 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12246 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12246 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12246 BstLean.Part154.csC) (piBar (rhoBar 12246 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12246 BstLean.Part154.csC) (piBar (rhoBar 12246 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12246 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199655466 : ℝ) ^ 2 + 0.000127042026 ^ 2 + 3 * 0.000073748782 ^ 2 +
        2 * 0.797885 * 0.000199655466 * 0.000127042026 + 2 * 0.000199655466 * 0.000073748782 +
        4 * 0.797885 * 0.000127042026 * 0.000073748782 := by gcongr
    _ ≤ (1.72146E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12246 BstLean.Part154.csC Θ ≤ 0.002730520999 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12246 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12246 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12246 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12246 BstLean.Part154.csC) (piBar (rhoBar 12246 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12246 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72146E-7 / (0.000261386292 : ℝ) := by gcongr
    _ ≤ 0.002730520999 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12246 BstLean.Part154.csC Θ ≤ 0.003031601663 + 0.000689935603 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12246 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12246 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12246 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261394804 +
        (6863 / 10000) * 0.000261394804 * 12246 * 0.001045647544) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003031601663 + 0.000689935603 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12246 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12246 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12246 0.011 Θ ∧ gammaRatio 12246 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12246 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12246) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12246 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12246 0.011 Θ) :=
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
    badAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12246 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12246 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12246 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12246 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12246 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12246 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12246 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12246 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12246 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12246 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12246 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004131601663 + 0.003420456602 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12246

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12246
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12246 BstLean.Part154.csC) (piBar (rhoBar 12246 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12246 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12246 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12246 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12246 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12246 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12246 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12246 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12246 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12246 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12246 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12246 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12246 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053458988718 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12246) ≤ 0.010791792994 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12246 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010791792994 + 2 * 0.737676 / 12246) := by gcongr
    _ ≤ (0.053458988718 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12246 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12246

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12246
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482275902 : ℝ) ≤ plow 12246 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12246) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433941380)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433523525) : eMP 12246 0.011 xi bn ≤ 0.001233445485 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12246 : ℝ) * (1 - 0.011))) ≤ 0.000609792529 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001433523525 / (12246 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609792529 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609792529 : ℝ) + 3.141593 * 0.053433941380 / (12246 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001233445485 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433941380)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433523525) : PiBarMP 12246 12 0.011 xi bn ≤ 0.164246297660 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12246 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037861900706 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.051324390031 : ℝ) ≤ √((12246 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.661646472479 : ℝ) ≤ √12246 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12246) ≤ 0.125900966658 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037861900706 + 0.053433941380 * 1.772454 / (2 * (110.051324390031 : ℝ))) * (1 + 0.001233445485) +
        8 / (12246 * 110.661646472479) + 0.125900966658 := by gcongr
    _ ≤ (0.164246297660 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433941380)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433523525) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284616816576) :
    parallelOracle 12246 0.011 xi bn cd ≤ 0.165276174919 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12246 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12246 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482275902 : ℝ) ≤ plow 12246 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.661646472479 : ℝ) ≤ √12246 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284616816576 : ℝ) / (2 * 0.560482275902 * 110.661646472479)) * 0.164246297660 +
        0.284616816576 ^ 2 / (2 * 0.560482275902 * 110.661646472479) := by gcongr
    _ ≤ (0.165276174919 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433941380) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433523525)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284616816576) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12246 12246 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482275902 : ℝ) ≤ plow 12246 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.661646472479 : ℝ) ≤ √12246 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12246 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12246 Θ 1.22 ≤ 0.011983379448 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.661646472479 := by gcongr <;> linarith
      _ ≤ (0.011983379448 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12246 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12246 12246 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12246 12246 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12246 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12246 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12246 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12246 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165276174919 + 0.011983379448 + (0.008646 : ℝ) *
        (1 + 2 * (0.284616816576 + 0.011983379448) / (0.560482275902 * 110.661646472479))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12246]

end BstLean.Part264b.N12246

/-! The original eight local profiles supply actual 12246 moment certificates. -/
namespace BstLean.Part264b.N12246
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12246 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053433941380 ∧
    0 ≤ bN 12246 BstLean.Part154.csC (groupTheta g) ∧ bN 12246 BstLean.Part154.csC (groupTheta g) ≤ 0.001433523525 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12246 12246 0.011
      (momentAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12246 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12246 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12246 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231157827858 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12246 0.011
      (momentAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12246 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12246
/-! The actual computed-centre upper energy formula at 12246. -/
namespace BstLean.Part264b.N12246
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12246

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12246
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12246 cell12246)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086945932042
  | 2 => 0.087918648592
  | 3 => 0.088894373288
  | 4 => 0.089875603973
  | 5 => 0.090865318998
  | 6 => 0.091867042775
  | 7 => 0.092884916489
  | 8 => 0.093923773817
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12246 12246 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12246 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12246

/-! Actual upper energy certificates on all 43 source endpoints at 12246. -/
namespace BstLean.Part264b.N12246
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12246 cell12246)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12246 (gMinus 12246) (1 - (cell12246 i).lower) ≤ 1 ∧
    energyUpper 12246 (gMinus 12246) (BstLean.Part211.gPlus 12246)
      (finiteEnergy 12246 12246 0.011) (1 - (cell12246 i).lower) ≤
      (cell12246 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12246) (by norm_num)
        (q := 1 - (cell12246 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12246,cell12246]) (by norm_num [scalarRow12246,cell12246])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12246,cell12246])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12246

/-! Source-cell containment and simple scalar guards at 12246. -/
namespace BstLean.Part264b.N12246
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12246 cell12246)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12246 ⟨10,by decide⟩).lower ∧ (cell12246 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12246 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12246 ⟨11,by decide⟩).lower ∧ (cell12246 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12246 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12246 ⟨12,by decide⟩).lower ∧ (cell12246 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12246 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12246 ⟨13,by decide⟩).lower ∧ (cell12246 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12246 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12246 ⟨14,by decide⟩).lower ∧ (cell12246 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12246 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12246 ⟨15,by decide⟩).lower ∧ (cell12246 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12246 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12246 ⟨16,by decide⟩).lower ∧ (cell12246 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12246 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12246 ⟨17,by decide⟩).lower ∧ (cell12246 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12246 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12246 ⟨18,by decide⟩).lower ∧ (cell12246 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12246 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12246 ⟨19,by decide⟩).lower ∧ (cell12246 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12246 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12246 ⟨20,by decide⟩).lower ∧ (cell12246 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12246 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12246 ⟨21,by decide⟩).lower ∧ (cell12246 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12246 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12246 ⟨22,by decide⟩).lower ∧ (cell12246 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12246 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12246 ⟨23,by decide⟩).lower ∧ (cell12246 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12246 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12246 ⟨24,by decide⟩).lower ∧ (cell12246 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12246 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12246 ⟨25,by decide⟩).lower ∧ (cell12246 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12246 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12246 ⟨26,by decide⟩).lower ∧ (cell12246 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12246 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12246 ⟨27,by decide⟩).lower ∧ (cell12246 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12246 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12246 ⟨28,by decide⟩).lower ∧ (cell12246 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12246 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12246 ⟨29,by decide⟩).lower ∧ (cell12246 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12246 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12246 ⟨30,by decide⟩).lower ∧ (cell12246 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12246 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12246 ⟨31,by decide⟩).lower ∧ (cell12246 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12246 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12246 ⟨32,by decide⟩).lower ∧ (cell12246 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12246 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12246 ⟨33,by decide⟩).lower ∧ (cell12246 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12246 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12246 ⟨34,by decide⟩).lower ∧ (cell12246 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12246 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12246 ⟨35,by decide⟩).lower ∧ (cell12246 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12246 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12246 ⟨36,by decide⟩).lower ∧ (cell12246 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12246 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12246 ⟨37,by decide⟩).lower ∧ (cell12246 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12246 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12246 ⟨38,by decide⟩).lower ∧ (cell12246 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12246 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12246 ⟨39,by decide⟩).lower ∧ (cell12246 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12246 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12246 ⟨40,by decide⟩).lower ∧ (cell12246 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12246 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12246 ⟨41,by decide⟩).lower ∧ (cell12246 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12246 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12246 ⟨42,by decide⟩).lower ∧ (cell12246 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12246 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12246 ⟨43,by decide⟩).lower ∧ (cell12246 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12246 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12246 ⟨44,by decide⟩).lower ∧ (cell12246 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12246 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12246 ⟨45,by decide⟩).lower ∧ (cell12246 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12246 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12246 ⟨46,by decide⟩).lower ∧ (cell12246 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12246 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12246 ⟨47,by decide⟩).lower ∧ (cell12246 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12246 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12246 ⟨48,by decide⟩).lower ∧ (cell12246 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12246 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12246 ⟨49,by decide⟩).lower ∧ (cell12246 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12246 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12246 ⟨50,by decide⟩).lower ∧ (cell12246 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12246 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12246 ⟨51,by decide⟩).lower ∧ (cell12246 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12246 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12246 ⟨52,by decide⟩).lower ∧ (cell12246 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12246 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12246 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12246 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12246,cell12246,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12246 i).lower ∧
    (cell12246 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12246 i).upper ≤ (0.532 : ℝ) ∧
    (cell12246 i).centre ≤ (0.1 : ℝ) ∧ (cell12246 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12246 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12246 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12246

/-! The local source numeric instances at 12246 have no network premises. -/
namespace BstLean.Part264b.N12246
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12246 cell12246)

noncomputable def sourceNumerics12246 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12246 (cell12246 i)
      scalarRow12246.M scalarRow12246.H scalarRow12246.xi := by
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
    energy_allowance := scalarRow12246.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12246]
    centre_nonneg := (scalarRow12246.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12246]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12246
/-! Actual 12247 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12247
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12247 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12247 12247 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12247.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12247 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12247 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12247 := gPlus_lower 12247
end BstLean.Part264b.N12247

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12247
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036471352872 : ℝ) ≤ wn 12247 := by
  have hn : √(12247 : ℝ) ≤ 110.666164657496 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12247 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.666164657496 ≤ 2 / √12247 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261364571 : ℝ) ≤ rhoBar 12247 BstLean.Part154.csC ∧
    rhoBar 12247 BstLean.Part154.csC ≤ 0.000261373460 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036471352872 : ℝ) / (1.295212 * 12247) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12247) := by gcongr
      _ ≤ (0.000261373460 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12247 BstLean.Part154.csC) ≤ 0.001045562157 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12247 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12247 BstLean.Part154.csC) (piBar (rhoBar 12247 BstLean.Part154.csC)) ≤ 0.000199639162 ∧
    cc1 (rhoBar 12247 BstLean.Part154.csC) (piBar (rhoBar 12247 BstLean.Part154.csC)) ≤ 0.000127031652 ∧
    cc2 (rhoBar 12247 BstLean.Part154.csC) ≤ 0.000073742760 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12247 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12247 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12247 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12247 BstLean.Part154.csC * nuR (rhoBar 12247 BstLean.Part154.csC)) ≤ 0.000522763999 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261373460 : ℝ) * 0.001045562157 := by gcongr
      _ ≤ (0.000522763999 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12247 BstLean.Part154.csC) * nuR (rhoBar 12247 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045562157 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12247 BstLean.Part154.csC) * rhoBar 12247 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261373460 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261373460 / 2 + 0.399 * 0.001045562157 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199639162 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522763999 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127031652 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261373460 / 1.414213562 := by gcongr
      _ ≤ (0.000073742760 : ℝ) := by norm_num

end BstLean.Part264b.N12247

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12247
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12247 BstLean.Part154.csC) (piBar (rhoBar 12247 BstLean.Part154.csC)) ≤ 1.72118E-7 := by
  have hr0 : 0 ≤ rhoBar 12247 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12247 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12247 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12247 BstLean.Part154.csC) (piBar (rhoBar 12247 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12247 BstLean.Part154.csC) (piBar (rhoBar 12247 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12247 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199639162 : ℝ) ^ 2 + 0.000127031652 ^ 2 + 3 * 0.000073742760 ^ 2 +
        2 * 0.797885 * 0.000199639162 * 0.000127031652 + 2 * 0.000199639162 * 0.000073742760 +
        4 * 0.797885 * 0.000127031652 * 0.000073742760 := by gcongr
    _ ≤ (1.72118E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12247 BstLean.Part154.csC Θ ≤ 0.002730303758 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12247 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12247 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12247 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12247 BstLean.Part154.csC) (piBar (rhoBar 12247 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12247 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72118E-7 / (0.000261364571 : ℝ) := by gcongr
    _ ≤ 0.002730303758 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12247 BstLean.Part154.csC Θ ≤ 0.003031354099 + 0.000689879267 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12247 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12247 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12247 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261373460 +
        (6863 / 10000) * 0.000261373460 * 12247 * 0.001045562157) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003031354099 + 0.000689879267 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12247 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12247 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12247 0.011 Θ ∧ gammaRatio 12247 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12247 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12247) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12247 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12247 0.011 Θ) :=
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
    badAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12247 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12247 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12247 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12247 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12247 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12247 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12247 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12247 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12247 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12247 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12247 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004131354099 + 0.003420183025 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12247

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12247
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12247 BstLean.Part154.csC) (piBar (rhoBar 12247 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12247 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12247 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12247 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12247 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12247 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12247 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12247 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12247 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12247 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12247 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12247 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12247 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053456782045 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12247) ≤ 0.010791352396 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12247 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010791352396 + 2 * 0.737676 / 12247) := by gcongr
    _ ≤ (0.053456782045 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12247 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12247

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12247
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482324536 : ℝ) ≤ plow 12247 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12247) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433550188)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433409473) : eMP 12247 0.011 xi bn ≤ 0.001233345945 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12247 : ℝ) * (1 - 0.011))) ≤ 0.000609743376 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001433409473 / (12247 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609743376 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609743376 : ℝ) + 3.141593 * 0.053433550188 / (12247 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001233345945 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433550188)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433409473) : PiBarMP 12247 12 0.011 xi bn ≤ 0.164239624158 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12247 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037860394518 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.055817656314 : ℝ) ≤ √((12247 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.666164657495 : ℝ) ≤ √12247 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12247) ≤ 0.125895826479 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037860394518 + 0.053433550188 * 1.772454 / (2 * (110.055817656314 : ℝ))) * (1 + 0.001233345945) +
        8 / (12247 * 110.666164657495) + 0.125895826479 := by gcongr
    _ ≤ (0.164239624158 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433550188)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433409473) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284613763744) :
    parallelOracle 12247 0.011 xi bn cd ≤ 0.165269425920 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12247 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12247 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482324536 : ℝ) ≤ plow 12247 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.666164657495 : ℝ) ≤ √12247 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284613763744 : ℝ) / (2 * 0.560482324536 * 110.666164657495)) * 0.164239624158 +
        0.284613763744 ^ 2 / (2 * 0.560482324536 * 110.666164657495) := by gcongr
    _ ≤ (0.165269425920 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433550188) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433409473)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284613763744) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12247 12247 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482324536 : ℝ) ≤ plow 12247 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.666164657495 : ℝ) ≤ √12247 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12247 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12247 Θ 1.22 ≤ 0.011982890201 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.666164657495 := by gcongr <;> linarith
      _ ≤ (0.011982890201 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12247 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12247 12247 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12247 12247 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12247 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12247 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12247 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12247 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165269425920 + 0.011982890201 + (0.008646 : ℝ) *
        (1 + 2 * (0.284613763744 + 0.011982890201) / (0.560482324536 * 110.666164657495))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12247]

end BstLean.Part264b.N12247

/-! The original eight local profiles supply actual 12247 moment certificates. -/
namespace BstLean.Part264b.N12247
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12247 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053433550188 ∧
    0 ≤ bN 12247 BstLean.Part154.csC (groupTheta g) ∧ bN 12247 BstLean.Part154.csC (groupTheta g) ≤ 0.001433409473 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12247 12247 0.011
      (momentAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12247 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12247 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12247 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231156981699 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12247 0.011
      (momentAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12247 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12247
/-! The actual computed-centre upper energy formula at 12247. -/
namespace BstLean.Part264b.N12247
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12247

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12247
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12247 cell12247)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086942385469
  | 2 => 0.087915020902
  | 3 => 0.088890650242
  | 4 => 0.089871768272
  | 5 => 0.090861349777
  | 6 => 0.091862915048
  | 7 => 0.092880600530
  | 8 => 0.093919234489
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12247 12247 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12247 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12247

/-! Actual upper energy certificates on all 43 source endpoints at 12247. -/
namespace BstLean.Part264b.N12247
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12247 cell12247)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12247 (gMinus 12247) (1 - (cell12247 i).lower) ≤ 1 ∧
    energyUpper 12247 (gMinus 12247) (BstLean.Part211.gPlus 12247)
      (finiteEnergy 12247 12247 0.011) (1 - (cell12247 i).lower) ≤
      (cell12247 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12247) (by norm_num)
        (q := 1 - (cell12247 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12247,cell12247]) (by norm_num [scalarRow12247,cell12247])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12247,cell12247])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12247

/-! Source-cell containment and simple scalar guards at 12247. -/
namespace BstLean.Part264b.N12247
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12247 cell12247)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12247 ⟨10,by decide⟩).lower ∧ (cell12247 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12247 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12247 ⟨11,by decide⟩).lower ∧ (cell12247 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12247 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12247 ⟨12,by decide⟩).lower ∧ (cell12247 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12247 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12247 ⟨13,by decide⟩).lower ∧ (cell12247 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12247 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12247 ⟨14,by decide⟩).lower ∧ (cell12247 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12247 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12247 ⟨15,by decide⟩).lower ∧ (cell12247 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12247 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12247 ⟨16,by decide⟩).lower ∧ (cell12247 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12247 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12247 ⟨17,by decide⟩).lower ∧ (cell12247 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12247 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12247 ⟨18,by decide⟩).lower ∧ (cell12247 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12247 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12247 ⟨19,by decide⟩).lower ∧ (cell12247 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12247 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12247 ⟨20,by decide⟩).lower ∧ (cell12247 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12247 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12247 ⟨21,by decide⟩).lower ∧ (cell12247 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12247 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12247 ⟨22,by decide⟩).lower ∧ (cell12247 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12247 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12247 ⟨23,by decide⟩).lower ∧ (cell12247 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12247 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12247 ⟨24,by decide⟩).lower ∧ (cell12247 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12247 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12247 ⟨25,by decide⟩).lower ∧ (cell12247 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12247 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12247 ⟨26,by decide⟩).lower ∧ (cell12247 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12247 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12247 ⟨27,by decide⟩).lower ∧ (cell12247 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12247 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12247 ⟨28,by decide⟩).lower ∧ (cell12247 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12247 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12247 ⟨29,by decide⟩).lower ∧ (cell12247 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12247 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12247 ⟨30,by decide⟩).lower ∧ (cell12247 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12247 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12247 ⟨31,by decide⟩).lower ∧ (cell12247 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12247 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12247 ⟨32,by decide⟩).lower ∧ (cell12247 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12247 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12247 ⟨33,by decide⟩).lower ∧ (cell12247 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12247 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12247 ⟨34,by decide⟩).lower ∧ (cell12247 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12247 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12247 ⟨35,by decide⟩).lower ∧ (cell12247 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12247 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12247 ⟨36,by decide⟩).lower ∧ (cell12247 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12247 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12247 ⟨37,by decide⟩).lower ∧ (cell12247 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12247 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12247 ⟨38,by decide⟩).lower ∧ (cell12247 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12247 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12247 ⟨39,by decide⟩).lower ∧ (cell12247 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12247 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12247 ⟨40,by decide⟩).lower ∧ (cell12247 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12247 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12247 ⟨41,by decide⟩).lower ∧ (cell12247 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12247 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12247 ⟨42,by decide⟩).lower ∧ (cell12247 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12247 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12247 ⟨43,by decide⟩).lower ∧ (cell12247 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12247 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12247 ⟨44,by decide⟩).lower ∧ (cell12247 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12247 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12247 ⟨45,by decide⟩).lower ∧ (cell12247 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12247 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12247 ⟨46,by decide⟩).lower ∧ (cell12247 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12247 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12247 ⟨47,by decide⟩).lower ∧ (cell12247 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12247 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12247 ⟨48,by decide⟩).lower ∧ (cell12247 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12247 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12247 ⟨49,by decide⟩).lower ∧ (cell12247 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12247 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12247 ⟨50,by decide⟩).lower ∧ (cell12247 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12247 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12247 ⟨51,by decide⟩).lower ∧ (cell12247 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12247 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12247 ⟨52,by decide⟩).lower ∧ (cell12247 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12247 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12247 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12247 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12247,cell12247,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12247 i).lower ∧
    (cell12247 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12247 i).upper ≤ (0.532 : ℝ) ∧
    (cell12247 i).centre ≤ (0.1 : ℝ) ∧ (cell12247 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12247 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12247 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12247

/-! The local source numeric instances at 12247 have no network premises. -/
namespace BstLean.Part264b.N12247
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12247 cell12247)

noncomputable def sourceNumerics12247 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12247 (cell12247 i)
      scalarRow12247.M scalarRow12247.H scalarRow12247.xi := by
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
    energy_allowance := scalarRow12247.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12247]
    centre_nonneg := (scalarRow12247.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12247]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12247
/-! Actual 12248 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12248
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12248 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12248 12248 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12248.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12248 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12248 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12248 := gPlus_lower 12248
end BstLean.Part264b.N12248

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12248
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036469850639 : ℝ) ≤ wn 12248 := by
  have hn : √(12248 : ℝ) ≤ 110.670682658056 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12248 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.670682658056 ≤ 2 / √12248 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261342852 : ℝ) ≤ rhoBar 12248 BstLean.Part154.csC ∧
    rhoBar 12248 BstLean.Part154.csC ≤ 0.000261352120 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036469850639 : ℝ) / (1.295212 * 12248) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12248) := by gcongr
      _ ≤ (0.000261352120 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12248 BstLean.Part154.csC) ≤ 0.001045476785 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12248 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12248 BstLean.Part154.csC) (piBar (rhoBar 12248 BstLean.Part154.csC)) ≤ 0.000199622861 ∧
    cc1 (rhoBar 12248 BstLean.Part154.csC) (piBar (rhoBar 12248 BstLean.Part154.csC)) ≤ 0.000127021280 ∧
    cc2 (rhoBar 12248 BstLean.Part154.csC) ≤ 0.000073736739 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12248 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12248 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12248 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12248 BstLean.Part154.csC * nuR (rhoBar 12248 BstLean.Part154.csC)) ≤ 0.000522721316 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261352120 : ℝ) * 0.001045476785 := by gcongr
      _ ≤ (0.000522721316 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12248 BstLean.Part154.csC) * nuR (rhoBar 12248 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045476785 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12248 BstLean.Part154.csC) * rhoBar 12248 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261352120 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261352120 / 2 + 0.399 * 0.001045476785 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199622861 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522721316 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127021280 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261352120 / 1.414213562 := by gcongr
      _ ≤ (0.000073736739 : ℝ) := by norm_num

end BstLean.Part264b.N12248

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12248
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12248 BstLean.Part154.csC) (piBar (rhoBar 12248 BstLean.Part154.csC)) ≤ 1.72090E-7 := by
  have hr0 : 0 ≤ rhoBar 12248 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12248 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12248 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12248 BstLean.Part154.csC) (piBar (rhoBar 12248 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12248 BstLean.Part154.csC) (piBar (rhoBar 12248 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12248 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199622861 : ℝ) ^ 2 + 0.000127021280 ^ 2 + 3 * 0.000073736739 ^ 2 +
        2 * 0.797885 * 0.000199622861 * 0.000127021280 + 2 * 0.000199622861 * 0.000073736739 +
        4 * 0.797885 * 0.000127021280 * 0.000073736739 := by gcongr
    _ ≤ (1.72090E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12248 BstLean.Part154.csC Θ ≤ 0.002730086461 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12248 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12248 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12248 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12248 BstLean.Part154.csC) (piBar (rhoBar 12248 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12248 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72090E-7 / (0.000261342852 : ℝ) := by gcongr
    _ ≤ 0.002730086461 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12248 BstLean.Part154.csC Θ ≤ 0.003031106585 + 0.000689822942 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12248 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12248 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12248 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261352120 +
        (6863 / 10000) * 0.000261352120 * 12248 * 0.001045476785) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003031106585 + 0.000689822942 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12248 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12248 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12248 0.011 Θ ∧ gammaRatio 12248 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12248 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12248) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12248 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12248 0.011 Θ) :=
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
    badAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12248 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12248 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12248 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12248 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12248 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12248 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12248 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12248 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12248 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12248 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12248 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004131106585 + 0.003419909403 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12248

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12248
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12248 BstLean.Part154.csC) (piBar (rhoBar 12248 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12248 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12248 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12248 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12248 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12248 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12248 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12248 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12248 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12248 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12248 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12248 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12248 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053454575645 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12248) ≤ 0.010790911852 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12248 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010790911852 + 2 * 0.737676 / 12248) := by gcongr
    _ ≤ (0.053454575645 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12248 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12248

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12248
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482373162 : ℝ) ≤ plow 12248 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12248) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433159022)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433295393) : eMP 12248 0.011 xi bn ≤ 0.001233246402 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12248 : ℝ) * (1 - 0.011))) ≤ 0.000609694221 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001433295393 / (12248 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609694221 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609694221 : ℝ) + 3.141593 * 0.053433159022 / (12248 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001233246402 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433159022)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433295393) : PiBarMP 12248 12 0.011 xi bn ≤ 0.164232950857 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12248 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037858887900 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.060310739157 : ℝ) ≤ √((12248 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.670682658055 : ℝ) ≤ √12248 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12248) ≤ 0.125890686930 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037858887900 + 0.053433159022 * 1.772454 / (2 * (110.060310739157 : ℝ))) * (1 + 0.001233246402) +
        8 / (12248 * 110.670682658055) + 0.125890686930 := by gcongr
    _ ≤ (0.164232950857 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433159022)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433295393) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284610711238) :
    parallelOracle 12248 0.011 xi bn cd ≤ 0.165262677132 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12248 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12248 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482373162 : ℝ) ≤ plow 12248 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.670682658055 : ℝ) ≤ √12248 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284610711238 : ℝ) / (2 * 0.560482373162 * 110.670682658055)) * 0.164232950857 +
        0.284610711238 ^ 2 / (2 * 0.560482373162 * 110.670682658055) := by gcongr
    _ ≤ (0.165262677132 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053433159022) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433295393)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284610711238) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12248 12248 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482373162 : ℝ) ≤ plow 12248 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.670682658055 : ℝ) ≤ √12248 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12248 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12248 Θ 1.22 ≤ 0.011982401014 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.670682658055 := by gcongr <;> linarith
      _ ≤ (0.011982401014 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12248 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12248 12248 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12248 12248 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12248 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12248 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12248 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12248 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165262677132 + 0.011982401014 + (0.008646 : ℝ) *
        (1 + 2 * (0.284610711238 + 0.011982401014) / (0.560482373162 * 110.670682658055))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12248]

end BstLean.Part264b.N12248

/-! The original eight local profiles supply actual 12248 moment certificates. -/
namespace BstLean.Part264b.N12248
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12248 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053433159022 ∧
    0 ≤ bN 12248 BstLean.Part154.csC (groupTheta g) ∧ bN 12248 BstLean.Part154.csC (groupTheta g) ≤ 0.001433295393 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12248 12248 0.011
      (momentAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12248 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12248 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12248 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231156135593 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12248 0.011
      (momentAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12248 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12248
/-! The actual computed-centre upper energy formula at 12248. -/
namespace BstLean.Part264b.N12248
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12248

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12248
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12248 cell12248)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086938840658
  | 2 => 0.087911395053
  | 3 => 0.088886929137
  | 4 => 0.089867934633
  | 5 => 0.090857382766
  | 6 => 0.091858789709
  | 7 => 0.092876287174
  | 8 => 0.093914698020
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12248 12248 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12248 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12248

/-! Actual upper energy certificates on all 43 source endpoints at 12248. -/
namespace BstLean.Part264b.N12248
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12248 cell12248)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12248 (gMinus 12248) (1 - (cell12248 i).lower) ≤ 1 ∧
    energyUpper 12248 (gMinus 12248) (BstLean.Part211.gPlus 12248)
      (finiteEnergy 12248 12248 0.011) (1 - (cell12248 i).lower) ≤
      (cell12248 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12248) (by norm_num)
        (q := 1 - (cell12248 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12248,cell12248]) (by norm_num [scalarRow12248,cell12248])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12248,cell12248])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12248

/-! Source-cell containment and simple scalar guards at 12248. -/
namespace BstLean.Part264b.N12248
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12248 cell12248)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12248 ⟨10,by decide⟩).lower ∧ (cell12248 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12248 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12248 ⟨11,by decide⟩).lower ∧ (cell12248 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12248 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12248 ⟨12,by decide⟩).lower ∧ (cell12248 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12248 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12248 ⟨13,by decide⟩).lower ∧ (cell12248 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12248 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12248 ⟨14,by decide⟩).lower ∧ (cell12248 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12248 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12248 ⟨15,by decide⟩).lower ∧ (cell12248 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12248 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12248 ⟨16,by decide⟩).lower ∧ (cell12248 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12248 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12248 ⟨17,by decide⟩).lower ∧ (cell12248 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12248 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12248 ⟨18,by decide⟩).lower ∧ (cell12248 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12248 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12248 ⟨19,by decide⟩).lower ∧ (cell12248 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12248 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12248 ⟨20,by decide⟩).lower ∧ (cell12248 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12248 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12248 ⟨21,by decide⟩).lower ∧ (cell12248 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12248 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12248 ⟨22,by decide⟩).lower ∧ (cell12248 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12248 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12248 ⟨23,by decide⟩).lower ∧ (cell12248 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12248 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12248 ⟨24,by decide⟩).lower ∧ (cell12248 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12248 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12248 ⟨25,by decide⟩).lower ∧ (cell12248 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12248 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12248 ⟨26,by decide⟩).lower ∧ (cell12248 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12248 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12248 ⟨27,by decide⟩).lower ∧ (cell12248 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12248 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12248 ⟨28,by decide⟩).lower ∧ (cell12248 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12248 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12248 ⟨29,by decide⟩).lower ∧ (cell12248 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12248 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12248 ⟨30,by decide⟩).lower ∧ (cell12248 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12248 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12248 ⟨31,by decide⟩).lower ∧ (cell12248 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12248 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12248 ⟨32,by decide⟩).lower ∧ (cell12248 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12248 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12248 ⟨33,by decide⟩).lower ∧ (cell12248 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12248 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12248 ⟨34,by decide⟩).lower ∧ (cell12248 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12248 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12248 ⟨35,by decide⟩).lower ∧ (cell12248 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12248 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12248 ⟨36,by decide⟩).lower ∧ (cell12248 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12248 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12248 ⟨37,by decide⟩).lower ∧ (cell12248 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12248 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12248 ⟨38,by decide⟩).lower ∧ (cell12248 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12248 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12248 ⟨39,by decide⟩).lower ∧ (cell12248 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12248 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12248 ⟨40,by decide⟩).lower ∧ (cell12248 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12248 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12248 ⟨41,by decide⟩).lower ∧ (cell12248 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12248 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12248 ⟨42,by decide⟩).lower ∧ (cell12248 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12248 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12248 ⟨43,by decide⟩).lower ∧ (cell12248 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12248 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12248 ⟨44,by decide⟩).lower ∧ (cell12248 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12248 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12248 ⟨45,by decide⟩).lower ∧ (cell12248 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12248 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12248 ⟨46,by decide⟩).lower ∧ (cell12248 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12248 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12248 ⟨47,by decide⟩).lower ∧ (cell12248 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12248 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12248 ⟨48,by decide⟩).lower ∧ (cell12248 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12248 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12248 ⟨49,by decide⟩).lower ∧ (cell12248 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12248 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12248 ⟨50,by decide⟩).lower ∧ (cell12248 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12248 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12248 ⟨51,by decide⟩).lower ∧ (cell12248 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12248 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12248 ⟨52,by decide⟩).lower ∧ (cell12248 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12248 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12248 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12248 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12248,cell12248,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12248 i).lower ∧
    (cell12248 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12248 i).upper ≤ (0.532 : ℝ) ∧
    (cell12248 i).centre ≤ (0.1 : ℝ) ∧ (cell12248 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12248 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12248 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12248

/-! The local source numeric instances at 12248 have no network premises. -/
namespace BstLean.Part264b.N12248
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12248 cell12248)

noncomputable def sourceNumerics12248 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12248 (cell12248 i)
      scalarRow12248.M scalarRow12248.H scalarRow12248.xi := by
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
    energy_allowance := scalarRow12248.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12248]
    centre_nonneg := (scalarRow12248.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12248]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12248
/-! Actual 12249 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12249
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12249 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12249 12249 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12249.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12249 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12249 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12249 := gPlus_lower 12249
end BstLean.Part264b.N12249

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12249
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036468348591 : ℝ) ≤ wn 12249 := by
  have hn : √(12249 : ℝ) ≤ 110.675200474181 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12249 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.675200474181 ≤ 2 / √12249 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261321138 : ℝ) ≤ rhoBar 12249 BstLean.Part154.csC ∧
    rhoBar 12249 BstLean.Part154.csC ≤ 0.000261330783 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036468348591 : ℝ) / (1.295212 * 12249) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12249) := by gcongr
      _ ≤ (0.000261330783 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12249 BstLean.Part154.csC) ≤ 0.001045391426 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12249 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12249 BstLean.Part154.csC) (piBar (rhoBar 12249 BstLean.Part154.csC)) ≤ 0.000199606563 ∧
    cc1 (rhoBar 12249 BstLean.Part154.csC) (piBar (rhoBar 12249 BstLean.Part154.csC)) ≤ 0.000127010910 ∧
    cc2 (rhoBar 12249 BstLean.Part154.csC) ≤ 0.000073730719 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12249 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12249 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12249 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12249 BstLean.Part154.csC * nuR (rhoBar 12249 BstLean.Part154.csC)) ≤ 0.000522678640 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261330783 : ℝ) * 0.001045391426 := by gcongr
      _ ≤ (0.000522678640 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12249 BstLean.Part154.csC) * nuR (rhoBar 12249 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045391426 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12249 BstLean.Part154.csC) * rhoBar 12249 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261330783 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261330783 / 2 + 0.399 * 0.001045391426 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199606563 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522678640 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127010910 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261330783 / 1.414213562 := by gcongr
      _ ≤ (0.000073730719 : ℝ) := by norm_num

end BstLean.Part264b.N12249

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12249
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12249 BstLean.Part154.csC) (piBar (rhoBar 12249 BstLean.Part154.csC)) ≤ 1.72062E-7 := by
  have hr0 : 0 ≤ rhoBar 12249 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12249 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12249 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12249 BstLean.Part154.csC) (piBar (rhoBar 12249 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12249 BstLean.Part154.csC) (piBar (rhoBar 12249 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12249 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199606563 : ℝ) ^ 2 + 0.000127010910 ^ 2 + 3 * 0.000073730719 ^ 2 +
        2 * 0.797885 * 0.000199606563 * 0.000127010910 + 2 * 0.000199606563 * 0.000073730719 +
        4 * 0.797885 * 0.000127010910 * 0.000073730719 := by gcongr
    _ ≤ (1.72062E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12249 BstLean.Part154.csC Θ ≤ 0.002729869075 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12249 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12249 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12249 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12249 BstLean.Part154.csC) (piBar (rhoBar 12249 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12249 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72062E-7 / (0.000261321138 : ℝ) := by gcongr
    _ ≤ 0.002729869075 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12249 BstLean.Part154.csC Θ ≤ 0.003030859103 + 0.000689766624 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12249 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12249 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12249 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261330783 +
        (6863 / 10000) * 0.000261330783 * 12249 * 0.001045391426) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003030859103 + 0.000689766624 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12249 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12249 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12249 0.011 Θ ∧ gammaRatio 12249 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12249 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12249) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12249 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12249 0.011 Θ) :=
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
    badAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12249 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12249 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12249 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12249 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12249 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12249 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12249 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12249 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12249 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12249 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12249 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004130859103 + 0.003419635699 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12249

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12249
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12249 BstLean.Part154.csC) (piBar (rhoBar 12249 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12249 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12249 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12249 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12249 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12249 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12249 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12249 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12249 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12249 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12249 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12249 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12249 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053452369512 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12249) ≤ 0.010790471361 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12249 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010790471361 + 2 * 0.737676 / 12249) := by gcongr
    _ ≤ (0.053452369512 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12249 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12249

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12249
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482421781 : ℝ) ≤ plow 12249 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12249) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053432767845)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433181265) : eMP 12249 0.011 xi bn ≤ 0.001233146848 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12249 : ℝ) * (1 - 0.011))) ≤ 0.000609645060 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001433181265 / (12249 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609645060 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609645060 : ℝ) + 3.141593 * 0.053432767845 / (12249 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001233146848 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053432767845)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433181265) : PiBarMP 12249 12 0.011 xi bn ≤ 0.164226277495 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12249 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037857380589 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.064803638583 : ℝ) ≤ √((12249 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.675200474180 : ℝ) ≤ √12249 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12249) ≤ 0.125885548010 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037857380589 + 0.053432767845 * 1.772454 / (2 * (110.064803638583 : ℝ))) * (1 + 0.001233146848) +
        8 / (12249 * 110.675200474180) + 0.125885548010 := by gcongr
    _ ≤ (0.164226277495 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053432767845)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433181265) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284607658972) :
    parallelOracle 12249 0.011 xi bn cd ≤ 0.165255928293 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12249 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12249 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482421781 : ℝ) ≤ plow 12249 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.675200474180 : ℝ) ≤ √12249 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284607658972 : ℝ) / (2 * 0.560482421781 * 110.675200474180)) * 0.164226277495 +
        0.284607658972 ^ 2 / (2 * 0.560482421781 * 110.675200474180) := by gcongr
    _ ≤ (0.165255928293 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053432767845) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433181265)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284607658972) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12249 12249 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482421781 : ℝ) ≤ plow 12249 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.675200474180 : ℝ) ≤ √12249 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12249 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12249 Θ 1.22 ≤ 0.011981911886 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.675200474180 := by gcongr <;> linarith
      _ ≤ (0.011981911886 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12249 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12249 12249 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12249 12249 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12249 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12249 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12249 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12249 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165255928293 + 0.011981911886 + (0.008646 : ℝ) *
        (1 + 2 * (0.284607658972 + 0.011981911886) / (0.560482421781 * 110.675200474180))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12249]

end BstLean.Part264b.N12249

/-! The original eight local profiles supply actual 12249 moment certificates. -/
namespace BstLean.Part264b.N12249
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12249 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053432767845 ∧
    0 ≤ bN 12249 BstLean.Part154.csC (groupTheta g) ∧ bN 12249 BstLean.Part154.csC (groupTheta g) ≤ 0.001433181265 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12249 12249 0.011
      (momentAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12249 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12249 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12249 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231155289460 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12249 0.011
      (momentAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12249 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12249
/-! The actual computed-centre upper energy formula at 12249. -/
namespace BstLean.Part264b.N12249
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12249

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12249
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12249 cell12249)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086935297605
  | 2 => 0.087907771044
  | 3 => 0.088883209970
  | 4 => 0.089864103054
  | 5 => 0.090853417963
  | 6 => 0.091854666756
  | 7 => 0.092871976417
  | 8 => 0.093910164406
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12249 12249 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12249 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12249

/-! Actual upper energy certificates on all 43 source endpoints at 12249. -/
namespace BstLean.Part264b.N12249
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12249 cell12249)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12249 (gMinus 12249) (1 - (cell12249 i).lower) ≤ 1 ∧
    energyUpper 12249 (gMinus 12249) (BstLean.Part211.gPlus 12249)
      (finiteEnergy 12249 12249 0.011) (1 - (cell12249 i).lower) ≤
      (cell12249 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12249) (by norm_num)
        (q := 1 - (cell12249 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12249,cell12249]) (by norm_num [scalarRow12249,cell12249])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12249,cell12249])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12249

/-! Source-cell containment and simple scalar guards at 12249. -/
namespace BstLean.Part264b.N12249
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12249 cell12249)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12249 ⟨10,by decide⟩).lower ∧ (cell12249 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12249 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12249 ⟨11,by decide⟩).lower ∧ (cell12249 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12249 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12249 ⟨12,by decide⟩).lower ∧ (cell12249 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12249 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12249 ⟨13,by decide⟩).lower ∧ (cell12249 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12249 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12249 ⟨14,by decide⟩).lower ∧ (cell12249 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12249 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12249 ⟨15,by decide⟩).lower ∧ (cell12249 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12249 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12249 ⟨16,by decide⟩).lower ∧ (cell12249 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12249 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12249 ⟨17,by decide⟩).lower ∧ (cell12249 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12249 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12249 ⟨18,by decide⟩).lower ∧ (cell12249 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12249 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12249 ⟨19,by decide⟩).lower ∧ (cell12249 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12249 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12249 ⟨20,by decide⟩).lower ∧ (cell12249 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12249 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12249 ⟨21,by decide⟩).lower ∧ (cell12249 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12249 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12249 ⟨22,by decide⟩).lower ∧ (cell12249 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12249 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12249 ⟨23,by decide⟩).lower ∧ (cell12249 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12249 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12249 ⟨24,by decide⟩).lower ∧ (cell12249 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12249 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12249 ⟨25,by decide⟩).lower ∧ (cell12249 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12249 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12249 ⟨26,by decide⟩).lower ∧ (cell12249 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12249 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12249 ⟨27,by decide⟩).lower ∧ (cell12249 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12249 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12249 ⟨28,by decide⟩).lower ∧ (cell12249 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12249 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12249 ⟨29,by decide⟩).lower ∧ (cell12249 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12249 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12249 ⟨30,by decide⟩).lower ∧ (cell12249 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12249 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12249 ⟨31,by decide⟩).lower ∧ (cell12249 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12249 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12249 ⟨32,by decide⟩).lower ∧ (cell12249 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12249 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12249 ⟨33,by decide⟩).lower ∧ (cell12249 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12249 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12249 ⟨34,by decide⟩).lower ∧ (cell12249 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12249 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12249 ⟨35,by decide⟩).lower ∧ (cell12249 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12249 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12249 ⟨36,by decide⟩).lower ∧ (cell12249 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12249 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12249 ⟨37,by decide⟩).lower ∧ (cell12249 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12249 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12249 ⟨38,by decide⟩).lower ∧ (cell12249 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12249 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12249 ⟨39,by decide⟩).lower ∧ (cell12249 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12249 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12249 ⟨40,by decide⟩).lower ∧ (cell12249 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12249 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12249 ⟨41,by decide⟩).lower ∧ (cell12249 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12249 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12249 ⟨42,by decide⟩).lower ∧ (cell12249 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12249 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12249 ⟨43,by decide⟩).lower ∧ (cell12249 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12249 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12249 ⟨44,by decide⟩).lower ∧ (cell12249 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12249 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12249 ⟨45,by decide⟩).lower ∧ (cell12249 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12249 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12249 ⟨46,by decide⟩).lower ∧ (cell12249 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12249 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12249 ⟨47,by decide⟩).lower ∧ (cell12249 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12249 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12249 ⟨48,by decide⟩).lower ∧ (cell12249 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12249 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12249 ⟨49,by decide⟩).lower ∧ (cell12249 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12249 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12249 ⟨50,by decide⟩).lower ∧ (cell12249 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12249 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12249 ⟨51,by decide⟩).lower ∧ (cell12249 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12249 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12249 ⟨52,by decide⟩).lower ∧ (cell12249 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12249 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12249 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12249 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12249,cell12249,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12249 i).lower ∧
    (cell12249 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12249 i).upper ≤ (0.532 : ℝ) ∧
    (cell12249 i).centre ≤ (0.1 : ℝ) ∧ (cell12249 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12249 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12249 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12249

/-! The local source numeric instances at 12249 have no network premises. -/
namespace BstLean.Part264b.N12249
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12249 cell12249)

noncomputable def sourceNumerics12249 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12249 (cell12249 i)
      scalarRow12249.M scalarRow12249.H scalarRow12249.xi := by
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
    energy_allowance := scalarRow12249.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12249]
    centre_nonneg := (scalarRow12249.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12249]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12249
