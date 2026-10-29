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
namespace BstLean.Part264b.N12275
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12275 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12275 12275 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12275.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12275 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12275 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12275 := gPlus_lower 12275
end BstLean.Part264b.N12275

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12275
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036429360172 : ℝ) ≤ wn 12275 := by
  have hn : √(12275 : ℝ) ≤ 110.792599030802 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12275 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.792599030802 ≤ 2 / √12275 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260757818 : ℝ) ≤ rhoBar 12275 BstLean.Part154.csC ∧
    rhoBar 12275 BstLean.Part154.csC ≤ 0.000260777252 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036429360172 : ℝ) / (1.295212 * 12275) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12275) := by gcongr
      _ ≤ (0.000260777252 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12275 BstLean.Part154.csC) ≤ 0.001043177013 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12275 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12275 BstLean.Part154.csC) (piBar (rhoBar 12275 BstLean.Part154.csC)) ≤ 0.000199183752 ∧
    cc1 (rhoBar 12275 BstLean.Part154.csC) (piBar (rhoBar 12275 BstLean.Part154.csC)) ≤ 0.000126741876 ∧
    cc2 (rhoBar 12275 BstLean.Part154.csC) ≤ 0.000073574548 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12275 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12275 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12275 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12275 BstLean.Part154.csC * nuR (rhoBar 12275 BstLean.Part154.csC)) ≤ 0.000521571505 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260777252 : ℝ) * 0.001043177013 := by gcongr
      _ ≤ (0.000521571505 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12275 BstLean.Part154.csC) * nuR (rhoBar 12275 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043177013 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12275 BstLean.Part154.csC) * rhoBar 12275 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260777252 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260777252 / 2 + 0.399 * 0.001043177013 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199183752 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521571505 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126741876 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260777252 / 1.414213562 := by gcongr
      _ ≤ (0.000073574548 : ℝ) := by norm_num

end BstLean.Part264b.N12275

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12275
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12275 BstLean.Part154.csC) (piBar (rhoBar 12275 BstLean.Part154.csC)) ≤ 1.71334E-7 := by
  have hr0 : 0 ≤ rhoBar 12275 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12275 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12275 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12275 BstLean.Part154.csC) (piBar (rhoBar 12275 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12275 BstLean.Part154.csC) (piBar (rhoBar 12275 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12275 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199183752 : ℝ) ^ 2 + 0.000126741876 ^ 2 + 3 * 0.000073574548 ^ 2 +
        2 * 0.797885 * 0.000199183752 * 0.000126741876 + 2 * 0.000199183752 * 0.000073574548 +
        4 * 0.797885 * 0.000126741876 * 0.000073574548 := by gcongr
    _ ≤ (1.71334E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12275 BstLean.Part154.csC Θ ≤ 0.002724191345 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12275 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12275 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12275 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12275 BstLean.Part154.csC) (piBar (rhoBar 12275 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12275 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71334E-7 / (0.000260757818 : ℝ) := by gcongr
    _ ≤ 0.002724191345 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12275 BstLean.Part154.csC Θ ≤ 0.003024438956 + 0.000688305613 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12275 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12275 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12275 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260777252 +
        (6863 / 10000) * 0.000260777252 * 12275 * 0.001043177013) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003024438956 + 0.000688305613 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12275 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12275 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12275 0.011 Θ ∧ gammaRatio 12275 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12275 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12275) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12275 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12275 0.011 Θ) :=
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
    badAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12275 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12275 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12275 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12275 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12275 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12275 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12275 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12275 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12275 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12275 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12275 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004124438956 + 0.003412496958 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12275

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12275
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12275 BstLean.Part154.csC) (piBar (rhoBar 12275 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12275 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12275 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12275 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12275 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12275 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12275 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12275 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12275 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12275 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12275 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12275 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12275 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053395105484 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12275) ≤ 0.010779037513 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12275 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010779037513 + 2 * 0.737676 / 12275) := by gcongr
    _ ≤ (0.053395105484 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12275 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12275

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12275
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483683079 : ℝ) ≤ plow 12275 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12275) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422599859)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430200457) : eMP 12275 0.011 xi bn ≤ 0.001230555586 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12275 : ℝ) * (1 - 0.011))) ≤ 0.000608365420 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001430200457 / (12275 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608365420 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608365420 : ℝ) + 3.141593 * 0.053422599859 / (12275 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001230555586 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422599859)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430200457) : PiBarMP 12275 12 0.011 xi bn ≤ 0.164052791916 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12275 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037817991182 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.181554717656 : ℝ) ≤ √((12275 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.792599030801 : ℝ) ≤ √12275 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12275) ≤ 0.125752156594 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037817991182 + 0.053422599859 * 1.772454 / (2 * (110.181554717656 : ℝ))) * (1 + 0.001230555586) +
        8 / (12275 * 110.792599030801) + 0.125752156594 := by gcongr
    _ ≤ (0.164052791916 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422599859)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430200457) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284528400055) :
    parallelOracle 12275 0.011 xi bn cd ≤ 0.165080483885 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12275 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12275 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483683079 : ℝ) ≤ plow 12275 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.792599030801 : ℝ) ≤ √12275 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284528400055 : ℝ) / (2 * 0.560483683079 * 110.792599030801)) * 0.164052791916 +
        0.284528400055 ^ 2 / (2 * 0.560483683079 * 110.792599030801) := by gcongr
    _ ≤ (0.165080483885 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422599859) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430200457)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284528400055) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12275 12275 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483683079 : ℝ) ≤ plow 12275 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.792599030801 : ℝ) ≤ √12275 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12275 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12275 Θ 1.22 ≤ 0.011969215558 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.792599030801 := by gcongr <;> linarith
      _ ≤ (0.011969215558 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12275 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12275 12275 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12275 12275 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12275 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12275 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12275 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12275 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165080483885 + 0.011969215558 + (0.008646 : ℝ) *
        (1 + 2 * (0.284528400055 + 0.011969215558) / (0.560483683079 * 110.792599030801))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12275]

end BstLean.Part264b.N12275

/-! The original eight local profiles supply actual 12275 moment certificates. -/
namespace BstLean.Part264b.N12275
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12275 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053422599859 ∧
    0 ≤ bN 12275 BstLean.Part154.csC (groupTheta g) ∧ bN 12275 BstLean.Part154.csC (groupTheta g) ≤ 0.001430200457 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12275 12275 0.011
      (momentAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12275 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12275 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12275 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231133294571 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12275 0.011
      (momentAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12275 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12275
/-! The actual computed-centre upper energy formula at 12275. -/
namespace BstLean.Part264b.N12275
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12275

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12275
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12275 cell12275)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086843789253
  | 2 => 0.087814185718
  | 3 => 0.088787184909
  | 4 => 0.089765197297
  | 5 => 0.090751099486
  | 6 => 0.091748298174
  | 7 => 0.092760799219
  | 8 => 0.093793281666
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12275 12275 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12275 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12275

/-! Actual upper energy certificates on all 43 source endpoints at 12275. -/
namespace BstLean.Part264b.N12275
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12275 cell12275)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12275 (gMinus 12275) (1 - (cell12275 i).lower) ≤ 1 ∧
    energyUpper 12275 (gMinus 12275) (BstLean.Part211.gPlus 12275)
      (finiteEnergy 12275 12275 0.011) (1 - (cell12275 i).lower) ≤
      (cell12275 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12275) (by norm_num)
        (q := 1 - (cell12275 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12275,cell12275]) (by norm_num [scalarRow12275,cell12275])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12275,cell12275])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12275

/-! Source-cell containment and simple scalar guards at 12275. -/
namespace BstLean.Part264b.N12275
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12275 cell12275)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12275 ⟨10,by decide⟩).lower ∧ (cell12275 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12275 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12275 ⟨11,by decide⟩).lower ∧ (cell12275 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12275 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12275 ⟨12,by decide⟩).lower ∧ (cell12275 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12275 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12275 ⟨13,by decide⟩).lower ∧ (cell12275 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12275 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12275 ⟨14,by decide⟩).lower ∧ (cell12275 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12275 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12275 ⟨15,by decide⟩).lower ∧ (cell12275 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12275 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12275 ⟨16,by decide⟩).lower ∧ (cell12275 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12275 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12275 ⟨17,by decide⟩).lower ∧ (cell12275 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12275 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12275 ⟨18,by decide⟩).lower ∧ (cell12275 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12275 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12275 ⟨19,by decide⟩).lower ∧ (cell12275 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12275 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12275 ⟨20,by decide⟩).lower ∧ (cell12275 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12275 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12275 ⟨21,by decide⟩).lower ∧ (cell12275 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12275 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12275 ⟨22,by decide⟩).lower ∧ (cell12275 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12275 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12275 ⟨23,by decide⟩).lower ∧ (cell12275 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12275 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12275 ⟨24,by decide⟩).lower ∧ (cell12275 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12275 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12275 ⟨25,by decide⟩).lower ∧ (cell12275 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12275 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12275 ⟨26,by decide⟩).lower ∧ (cell12275 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12275 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12275 ⟨27,by decide⟩).lower ∧ (cell12275 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12275 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12275 ⟨28,by decide⟩).lower ∧ (cell12275 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12275 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12275 ⟨29,by decide⟩).lower ∧ (cell12275 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12275 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12275 ⟨30,by decide⟩).lower ∧ (cell12275 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12275 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12275 ⟨31,by decide⟩).lower ∧ (cell12275 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12275 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12275 ⟨32,by decide⟩).lower ∧ (cell12275 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12275 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12275 ⟨33,by decide⟩).lower ∧ (cell12275 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12275 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12275 ⟨34,by decide⟩).lower ∧ (cell12275 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12275 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12275 ⟨35,by decide⟩).lower ∧ (cell12275 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12275 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12275 ⟨36,by decide⟩).lower ∧ (cell12275 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12275 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12275 ⟨37,by decide⟩).lower ∧ (cell12275 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12275 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12275 ⟨38,by decide⟩).lower ∧ (cell12275 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12275 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12275 ⟨39,by decide⟩).lower ∧ (cell12275 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12275 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12275 ⟨40,by decide⟩).lower ∧ (cell12275 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12275 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12275 ⟨41,by decide⟩).lower ∧ (cell12275 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12275 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12275 ⟨42,by decide⟩).lower ∧ (cell12275 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12275 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12275 ⟨43,by decide⟩).lower ∧ (cell12275 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12275 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12275 ⟨44,by decide⟩).lower ∧ (cell12275 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12275 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12275 ⟨45,by decide⟩).lower ∧ (cell12275 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12275 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12275 ⟨46,by decide⟩).lower ∧ (cell12275 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12275 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12275 ⟨47,by decide⟩).lower ∧ (cell12275 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12275 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12275 ⟨48,by decide⟩).lower ∧ (cell12275 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12275 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12275 ⟨49,by decide⟩).lower ∧ (cell12275 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12275 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12275 ⟨50,by decide⟩).lower ∧ (cell12275 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12275 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12275 ⟨51,by decide⟩).lower ∧ (cell12275 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12275 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12275 ⟨52,by decide⟩).lower ∧ (cell12275 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12275 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12275 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12275 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12275,cell12275,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12275 i).lower ∧
    (cell12275 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12275 i).upper ≤ (0.532 : ℝ) ∧
    (cell12275 i).centre ≤ (0.1 : ℝ) ∧ (cell12275 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12275 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12275 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12275

/-! The local source numeric instances at 12275 have no network premises. -/
namespace BstLean.Part264b.N12275
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12275 cell12275)

noncomputable def sourceNumerics12275 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12275 (cell12275 i)
      scalarRow12275.M scalarRow12275.H scalarRow12275.xi := by
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
    energy_allowance := scalarRow12275.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12275]
    centre_nonneg := (scalarRow12275.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12275]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12275
/-! Actual 12276 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12276
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12276 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12276 12276 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12276.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12276 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12276 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12276 := gPlus_lower 12276
end BstLean.Part264b.N12276

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12276
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036427863107 : ℝ) ≤ wn 12276 := by
  have hn : √(12276 : ℝ) ≤ 110.797111875717 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12276 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.797111875717 ≤ 2 / √12276 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260736200 : ℝ) ≤ rhoBar 12276 BstLean.Part154.csC ∧
    rhoBar 12276 BstLean.Part154.csC ≤ 0.000260756009 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036427863107 : ℝ) / (1.295212 * 12276) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12276) := by gcongr
      _ ≤ (0.000260756009 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12276 BstLean.Part154.csC) ≤ 0.001043092030 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12276 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12276 BstLean.Part154.csC) (piBar (rhoBar 12276 BstLean.Part154.csC)) ≤ 0.000199167525 ∧
    cc1 (rhoBar 12276 BstLean.Part154.csC) (piBar (rhoBar 12276 BstLean.Part154.csC)) ≤ 0.000126731552 ∧
    cc2 (rhoBar 12276 BstLean.Part154.csC) ≤ 0.000073568555 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12276 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12276 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12276 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12276 BstLean.Part154.csC * nuR (rhoBar 12276 BstLean.Part154.csC)) ≤ 0.000521529017 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260756009 : ℝ) * 0.001043092030 := by gcongr
      _ ≤ (0.000521529017 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12276 BstLean.Part154.csC) * nuR (rhoBar 12276 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043092030 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12276 BstLean.Part154.csC) * rhoBar 12276 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260756009 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260756009 / 2 + 0.399 * 0.001043092030 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199167525 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521529017 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126731552 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260756009 / 1.414213562 := by gcongr
      _ ≤ (0.000073568555 : ℝ) := by norm_num

end BstLean.Part264b.N12276

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12276
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12276 BstLean.Part154.csC) (piBar (rhoBar 12276 BstLean.Part154.csC)) ≤ 1.71306E-7 := by
  have hr0 : 0 ≤ rhoBar 12276 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12276 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12276 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12276 BstLean.Part154.csC) (piBar (rhoBar 12276 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12276 BstLean.Part154.csC) (piBar (rhoBar 12276 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12276 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199167525 : ℝ) ^ 2 + 0.000126731552 ^ 2 + 3 * 0.000073568555 ^ 2 +
        2 * 0.797885 * 0.000199167525 * 0.000126731552 + 2 * 0.000199167525 * 0.000073568555 +
        4 * 0.797885 * 0.000126731552 * 0.000073568555 := by gcongr
    _ ≤ (1.71306E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12276 BstLean.Part154.csC Θ ≤ 0.002723971977 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12276 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12276 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12276 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12276 BstLean.Part154.csC) (piBar (rhoBar 12276 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12276 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71306E-7 / (0.000260736200 : ℝ) := by gcongr
    _ ≤ 0.002723971977 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12276 BstLean.Part154.csC Θ ≤ 0.003024192566 + 0.000688249543 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12276 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12276 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12276 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260756009 +
        (6863 / 10000) * 0.000260756009 * 12276 * 0.001043092030) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003024192566 + 0.000688249543 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12276 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12276 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12276 0.011 Θ ∧ gammaRatio 12276 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12276 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12276) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12276 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12276 0.011 Θ) :=
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
    badAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12276 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12276 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12276 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12276 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12276 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12276 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12276 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12276 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12276 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12276 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12276 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004124192566 + 0.003412221520 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12276

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12276
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12276 BstLean.Part154.csC) (piBar (rhoBar 12276 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12276 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12276 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12276 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12276 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12276 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12276 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12276 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12276 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12276 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12276 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12276 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12276 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053392906681 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12276) ≤ 0.010778598475 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12276 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010778598475 + 2 * 0.737676 / 12276) := by gcongr
    _ ≤ (0.053392906681 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12276 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12276

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12276
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483731484 : ℝ) ≤ plow 12276 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12276) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422208864)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430085288) : eMP 12276 0.011 xi bn ≤ 0.001230455813 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12276 : ℝ) * (1 - 0.011))) ≤ 0.000608316147 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001430085288 / (12276 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608316147 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608316147 : ℝ) + 3.141593 * 0.053422208864 / (12276 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001230455813 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422208864)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430085288) : PiBarMP 12276 12 0.011 xi bn ≤ 0.164046120157 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12276 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037816468477 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.186042673289 : ℝ) ≤ √((12276 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.797111875716 : ℝ) ≤ √12276 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12276) ≤ 0.125747034620 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037816468477 + 0.053422208864 * 1.772454 / (2 * (110.186042673289 : ℝ))) * (1 + 0.001230455813) +
        8 / (12276 * 110.797111875716) + 0.125747034620 := by gcongr
    _ ≤ (0.164046120157 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422208864)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430085288) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284525355429) :
    parallelOracle 12276 0.011 xi bn cd ≤ 0.165073736923 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12276 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12276 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483731484 : ℝ) ≤ plow 12276 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.797111875716 : ℝ) ≤ √12276 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284525355429 : ℝ) / (2 * 0.560483731484 * 110.797111875716)) * 0.164046120157 +
        0.284525355429 ^ 2 / (2 * 0.560483731484 * 110.797111875716) := by gcongr
    _ ≤ (0.165073736923 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053422208864) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001430085288)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284525355429) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12276 12276 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483731484 : ℝ) ≤ plow 12276 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.797111875716 : ℝ) ≤ √12276 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12276 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12276 Θ 1.22 ≤ 0.011968728044 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.797111875716 := by gcongr <;> linarith
      _ ≤ (0.011968728044 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12276 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12276 12276 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12276 12276 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12276 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12276 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12276 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12276 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165073736923 + 0.011968728044 + (0.008646 : ℝ) *
        (1 + 2 * (0.284525355429 + 0.011968728044) / (0.560483731484 * 110.797111875716))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12276]

end BstLean.Part264b.N12276

/-! The original eight local profiles supply actual 12276 moment certificates. -/
namespace BstLean.Part264b.N12276
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12276 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053422208864 ∧
    0 ≤ bN 12276 BstLean.Part154.csC (groupTheta g) ∧ bN 12276 BstLean.Part154.csC (groupTheta g) ≤ 0.001430085288 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12276 12276 0.011
      (momentAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12276 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12276 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12276 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231132448748 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12276 0.011
      (momentAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12276 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12276
/-! The actual computed-centre upper energy formula at 12276. -/
namespace BstLean.Part264b.N12276
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12276

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12276
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12276 cell12276)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086840292957
  | 2 => 0.087810610598
  | 3 => 0.088783517258
  | 4 => 0.089761420448
  | 5 => 0.090747193320
  | 6 => 0.091744238585
  | 7 => 0.092756557506
  | 8 => 0.093788823883
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12276 12276 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12276 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12276

/-! Actual upper energy certificates on all 43 source endpoints at 12276. -/
namespace BstLean.Part264b.N12276
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12276 cell12276)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12276 (gMinus 12276) (1 - (cell12276 i).lower) ≤ 1 ∧
    energyUpper 12276 (gMinus 12276) (BstLean.Part211.gPlus 12276)
      (finiteEnergy 12276 12276 0.011) (1 - (cell12276 i).lower) ≤
      (cell12276 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12276) (by norm_num)
        (q := 1 - (cell12276 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12276,cell12276]) (by norm_num [scalarRow12276,cell12276])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12276,cell12276])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12276

/-! Source-cell containment and simple scalar guards at 12276. -/
namespace BstLean.Part264b.N12276
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12276 cell12276)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12276 ⟨10,by decide⟩).lower ∧ (cell12276 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12276 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12276 ⟨11,by decide⟩).lower ∧ (cell12276 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12276 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12276 ⟨12,by decide⟩).lower ∧ (cell12276 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12276 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12276 ⟨13,by decide⟩).lower ∧ (cell12276 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12276 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12276 ⟨14,by decide⟩).lower ∧ (cell12276 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12276 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12276 ⟨15,by decide⟩).lower ∧ (cell12276 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12276 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12276 ⟨16,by decide⟩).lower ∧ (cell12276 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12276 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12276 ⟨17,by decide⟩).lower ∧ (cell12276 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12276 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12276 ⟨18,by decide⟩).lower ∧ (cell12276 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12276 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12276 ⟨19,by decide⟩).lower ∧ (cell12276 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12276 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12276 ⟨20,by decide⟩).lower ∧ (cell12276 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12276 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12276 ⟨21,by decide⟩).lower ∧ (cell12276 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12276 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12276 ⟨22,by decide⟩).lower ∧ (cell12276 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12276 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12276 ⟨23,by decide⟩).lower ∧ (cell12276 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12276 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12276 ⟨24,by decide⟩).lower ∧ (cell12276 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12276 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12276 ⟨25,by decide⟩).lower ∧ (cell12276 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12276 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12276 ⟨26,by decide⟩).lower ∧ (cell12276 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12276 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12276 ⟨27,by decide⟩).lower ∧ (cell12276 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12276 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12276 ⟨28,by decide⟩).lower ∧ (cell12276 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12276 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12276 ⟨29,by decide⟩).lower ∧ (cell12276 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12276 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12276 ⟨30,by decide⟩).lower ∧ (cell12276 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12276 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12276 ⟨31,by decide⟩).lower ∧ (cell12276 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12276 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12276 ⟨32,by decide⟩).lower ∧ (cell12276 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12276 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12276 ⟨33,by decide⟩).lower ∧ (cell12276 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12276 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12276 ⟨34,by decide⟩).lower ∧ (cell12276 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12276 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12276 ⟨35,by decide⟩).lower ∧ (cell12276 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12276 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12276 ⟨36,by decide⟩).lower ∧ (cell12276 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12276 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12276 ⟨37,by decide⟩).lower ∧ (cell12276 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12276 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12276 ⟨38,by decide⟩).lower ∧ (cell12276 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12276 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12276 ⟨39,by decide⟩).lower ∧ (cell12276 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12276 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12276 ⟨40,by decide⟩).lower ∧ (cell12276 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12276 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12276 ⟨41,by decide⟩).lower ∧ (cell12276 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12276 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12276 ⟨42,by decide⟩).lower ∧ (cell12276 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12276 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12276 ⟨43,by decide⟩).lower ∧ (cell12276 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12276 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12276 ⟨44,by decide⟩).lower ∧ (cell12276 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12276 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12276 ⟨45,by decide⟩).lower ∧ (cell12276 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12276 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12276 ⟨46,by decide⟩).lower ∧ (cell12276 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12276 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12276 ⟨47,by decide⟩).lower ∧ (cell12276 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12276 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12276 ⟨48,by decide⟩).lower ∧ (cell12276 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12276 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12276 ⟨49,by decide⟩).lower ∧ (cell12276 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12276 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12276 ⟨50,by decide⟩).lower ∧ (cell12276 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12276 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12276 ⟨51,by decide⟩).lower ∧ (cell12276 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12276 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12276 ⟨52,by decide⟩).lower ∧ (cell12276 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12276 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12276 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12276 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12276,cell12276,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12276 i).lower ∧
    (cell12276 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12276 i).upper ≤ (0.532 : ℝ) ∧
    (cell12276 i).centre ≤ (0.1 : ℝ) ∧ (cell12276 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12276 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12276 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12276

/-! The local source numeric instances at 12276 have no network premises. -/
namespace BstLean.Part264b.N12276
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12276 cell12276)

noncomputable def sourceNumerics12276 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12276 (cell12276 i)
      scalarRow12276.M scalarRow12276.H scalarRow12276.xi := by
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
    energy_allowance := scalarRow12276.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12276]
    centre_nonneg := (scalarRow12276.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12276]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12276
/-! Actual 12277 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12277
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12277 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12277 12277 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12277.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12277 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12277 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12277 := gPlus_lower 12277
end BstLean.Part264b.N12277

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12277
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036426366225 : ℝ) ≤ wn 12277 := by
  have hn : √(12277 : ℝ) ≤ 110.801624536828 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12277 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.801624536828 ≤ 2 / √12277 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260714585 : ℝ) ≤ rhoBar 12277 BstLean.Part154.csC ∧
    rhoBar 12277 BstLean.Part154.csC ≤ 0.000260734769 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036426366225 : ℝ) / (1.295212 * 12277) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12277) := by gcongr
      _ ≤ (0.000260734769 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12277 BstLean.Part154.csC) ≤ 0.001043007059 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12277 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12277 BstLean.Part154.csC) (piBar (rhoBar 12277 BstLean.Part154.csC)) ≤ 0.000199151301 ∧
    cc1 (rhoBar 12277 BstLean.Part154.csC) (piBar (rhoBar 12277 BstLean.Part154.csC)) ≤ 0.000126721228 ∧
    cc2 (rhoBar 12277 BstLean.Part154.csC) ≤ 0.000073562562 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12277 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12277 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12277 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12277 BstLean.Part154.csC * nuR (rhoBar 12277 BstLean.Part154.csC)) ≤ 0.000521486534 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260734769 : ℝ) * 0.001043007059 := by gcongr
      _ ≤ (0.000521486534 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12277 BstLean.Part154.csC) * nuR (rhoBar 12277 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001043007059 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12277 BstLean.Part154.csC) * rhoBar 12277 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260734769 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260734769 / 2 + 0.399 * 0.001043007059 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199151301 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521486534 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126721228 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260734769 / 1.414213562 := by gcongr
      _ ≤ (0.000073562562 : ℝ) := by norm_num

end BstLean.Part264b.N12277

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12277
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12277 BstLean.Part154.csC) (piBar (rhoBar 12277 BstLean.Part154.csC)) ≤ 1.71278E-7 := by
  have hr0 : 0 ≤ rhoBar 12277 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12277 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12277 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12277 BstLean.Part154.csC) (piBar (rhoBar 12277 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12277 BstLean.Part154.csC) (piBar (rhoBar 12277 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12277 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199151301 : ℝ) ^ 2 + 0.000126721228 ^ 2 + 3 * 0.000073562562 ^ 2 +
        2 * 0.797885 * 0.000199151301 * 0.000126721228 + 2 * 0.000199151301 * 0.000073562562 +
        4 * 0.797885 * 0.000126721228 * 0.000073562562 := by gcongr
    _ ≤ (1.71278E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12277 BstLean.Part154.csC Θ ≤ 0.002723752542 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12277 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12277 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12277 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12277 BstLean.Part154.csC) (piBar (rhoBar 12277 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12277 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71278E-7 / (0.000260714585 : ℝ) := by gcongr
    _ ≤ 0.002723752542 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12277 BstLean.Part154.csC Θ ≤ 0.003023946207 + 0.000688193481 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12277 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12277 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12277 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260734769 +
        (6863 / 10000) * 0.000260734769 * 12277 * 0.001043007059) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003023946207 + 0.000688193481 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12277 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12277 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12277 0.011 Θ ∧ gammaRatio 12277 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12277 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12277) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12277 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12277 0.011 Θ) :=
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
    badAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12277 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12277 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12277 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12277 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12277 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12277 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12277 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12277 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12277 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12277 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12277 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004123946207 + 0.003411946023 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12277

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12277
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12277 BstLean.Part154.csC) (piBar (rhoBar 12277 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12277 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12277 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12277 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12277 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12277 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12277 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12277 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12277 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12277 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12277 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12277 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12277 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053390708150 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12277) ≤ 0.010778159491 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12277 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010778159491 + 2 * 0.737676 / 12277) := by gcongr
    _ ≤ (0.053390708150 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12277 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12277

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12277
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483779881 : ℝ) ≤ plow 12277 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12277) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421817870)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429970085) : eMP 12277 0.011 xi bn ≤ 0.001230356032 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12277 : ℝ) * (1 - 0.011))) ≤ 0.000608266870 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001429970085 / (12277 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608266870 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608266870 : ℝ) + 3.141593 * 0.053421817870 / (12277 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001230356032 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421817870)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429970085) : PiBarMP 12277 12 0.011 xi bn ≤ 0.164039448512 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12277 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037814945260 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.190530446132 : ℝ) ≤ √((12277 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.801624536827 : ℝ) ≤ √12277 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12277) ≤ 0.125741913271 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037814945260 + 0.053421817870 * 1.772454 / (2 * (110.190530446132 : ℝ))) * (1 + 0.001230356032) +
        8 / (12277 * 110.801624536827) + 0.125741913271 := by gcongr
    _ ≤ (0.164039448512 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421817870)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429970085) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284522311074) :
    parallelOracle 12277 0.011 xi bn cd ≤ 0.165066990086 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12277 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12277 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483779881 : ℝ) ≤ plow 12277 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.801624536827 : ℝ) ≤ √12277 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284522311074 : ℝ) / (2 * 0.560483779881 * 110.801624536827)) * 0.164039448512 +
        0.284522311074 ^ 2 / (2 * 0.560483779881 * 110.801624536827) := by gcongr
    _ ≤ (0.165066990086 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421817870) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429970085)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284522311074) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12277 12277 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483779881 : ℝ) ≤ plow 12277 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.801624536827 : ℝ) ≤ √12277 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12277 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12277 Θ 1.22 ≤ 0.011968240589 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.801624536827 := by gcongr <;> linarith
      _ ≤ (0.011968240589 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12277 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12277 12277 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12277 12277 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12277 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12277 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12277 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12277 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165066990086 + 0.011968240589 + (0.008646 : ℝ) *
        (1 + 2 * (0.284522311074 + 0.011968240589) / (0.560483779881 * 110.801624536827))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12277]

end BstLean.Part264b.N12277

/-! The original eight local profiles supply actual 12277 moment certificates. -/
namespace BstLean.Part264b.N12277
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12277 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053421817870 ∧
    0 ≤ bN 12277 BstLean.Part154.csC (groupTheta g) ∧ bN 12277 BstLean.Part154.csC (groupTheta g) ≤ 0.001429970085 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12277 12277 0.011
      (momentAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12277 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12277 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12277 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231131602924 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12277 0.011
      (momentAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12277 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12277
/-! The actual computed-centre upper energy formula at 12277. -/
namespace BstLean.Part264b.N12277
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12277

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12277
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12277 cell12277)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086836798366
  | 2 => 0.087807037261
  | 3 => 0.088779851485
  | 4 => 0.089757645593
  | 5 => 0.090743289292
  | 6 => 0.091740181304
  | 7 => 0.092752318308
  | 8 => 0.093784368862
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12277 12277 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12277 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12277

/-! Actual upper energy certificates on all 43 source endpoints at 12277. -/
namespace BstLean.Part264b.N12277
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12277 cell12277)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12277 (gMinus 12277) (1 - (cell12277 i).lower) ≤ 1 ∧
    energyUpper 12277 (gMinus 12277) (BstLean.Part211.gPlus 12277)
      (finiteEnergy 12277 12277 0.011) (1 - (cell12277 i).lower) ≤
      (cell12277 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12277) (by norm_num)
        (q := 1 - (cell12277 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12277,cell12277]) (by norm_num [scalarRow12277,cell12277])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12277,cell12277])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12277

/-! Source-cell containment and simple scalar guards at 12277. -/
namespace BstLean.Part264b.N12277
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12277 cell12277)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12277 ⟨10,by decide⟩).lower ∧ (cell12277 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12277 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12277 ⟨11,by decide⟩).lower ∧ (cell12277 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12277 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12277 ⟨12,by decide⟩).lower ∧ (cell12277 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12277 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12277 ⟨13,by decide⟩).lower ∧ (cell12277 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12277 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12277 ⟨14,by decide⟩).lower ∧ (cell12277 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12277 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12277 ⟨15,by decide⟩).lower ∧ (cell12277 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12277 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12277 ⟨16,by decide⟩).lower ∧ (cell12277 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12277 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12277 ⟨17,by decide⟩).lower ∧ (cell12277 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12277 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12277 ⟨18,by decide⟩).lower ∧ (cell12277 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12277 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12277 ⟨19,by decide⟩).lower ∧ (cell12277 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12277 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12277 ⟨20,by decide⟩).lower ∧ (cell12277 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12277 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12277 ⟨21,by decide⟩).lower ∧ (cell12277 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12277 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12277 ⟨22,by decide⟩).lower ∧ (cell12277 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12277 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12277 ⟨23,by decide⟩).lower ∧ (cell12277 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12277 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12277 ⟨24,by decide⟩).lower ∧ (cell12277 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12277 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12277 ⟨25,by decide⟩).lower ∧ (cell12277 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12277 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12277 ⟨26,by decide⟩).lower ∧ (cell12277 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12277 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12277 ⟨27,by decide⟩).lower ∧ (cell12277 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12277 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12277 ⟨28,by decide⟩).lower ∧ (cell12277 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12277 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12277 ⟨29,by decide⟩).lower ∧ (cell12277 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12277 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12277 ⟨30,by decide⟩).lower ∧ (cell12277 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12277 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12277 ⟨31,by decide⟩).lower ∧ (cell12277 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12277 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12277 ⟨32,by decide⟩).lower ∧ (cell12277 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12277 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12277 ⟨33,by decide⟩).lower ∧ (cell12277 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12277 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12277 ⟨34,by decide⟩).lower ∧ (cell12277 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12277 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12277 ⟨35,by decide⟩).lower ∧ (cell12277 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12277 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12277 ⟨36,by decide⟩).lower ∧ (cell12277 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12277 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12277 ⟨37,by decide⟩).lower ∧ (cell12277 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12277 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12277 ⟨38,by decide⟩).lower ∧ (cell12277 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12277 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12277 ⟨39,by decide⟩).lower ∧ (cell12277 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12277 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12277 ⟨40,by decide⟩).lower ∧ (cell12277 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12277 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12277 ⟨41,by decide⟩).lower ∧ (cell12277 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12277 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12277 ⟨42,by decide⟩).lower ∧ (cell12277 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12277 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12277 ⟨43,by decide⟩).lower ∧ (cell12277 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12277 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12277 ⟨44,by decide⟩).lower ∧ (cell12277 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12277 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12277 ⟨45,by decide⟩).lower ∧ (cell12277 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12277 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12277 ⟨46,by decide⟩).lower ∧ (cell12277 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12277 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12277 ⟨47,by decide⟩).lower ∧ (cell12277 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12277 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12277 ⟨48,by decide⟩).lower ∧ (cell12277 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12277 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12277 ⟨49,by decide⟩).lower ∧ (cell12277 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12277 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12277 ⟨50,by decide⟩).lower ∧ (cell12277 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12277 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12277 ⟨51,by decide⟩).lower ∧ (cell12277 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12277 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12277 ⟨52,by decide⟩).lower ∧ (cell12277 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12277 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12277 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12277 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12277,cell12277,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12277 i).lower ∧
    (cell12277 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12277 i).upper ≤ (0.532 : ℝ) ∧
    (cell12277 i).centre ≤ (0.1 : ℝ) ∧ (cell12277 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12277 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12277 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12277

/-! The local source numeric instances at 12277 have no network premises. -/
namespace BstLean.Part264b.N12277
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12277 cell12277)

noncomputable def sourceNumerics12277 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12277 (cell12277 i)
      scalarRow12277.M scalarRow12277.H scalarRow12277.xi := by
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
    energy_allowance := scalarRow12277.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12277]
    centre_nonneg := (scalarRow12277.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12277]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12277
/-! Actual 12278 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12278
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12278 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12278 12278 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12278.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12278 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12278 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12278 := gPlus_lower 12278
end BstLean.Part264b.N12278

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12278
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036424869527 : ℝ) ≤ wn 12278 := by
  have hn : √(12278 : ℝ) ≤ 110.806137014157 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12278 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.806137014157 ≤ 2 / √12278 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260692975 : ℝ) ≤ rhoBar 12278 BstLean.Part154.csC ∧
    rhoBar 12278 BstLean.Part154.csC ≤ 0.000260713533 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036424869527 : ℝ) / (1.295212 * 12278) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12278) := by gcongr
      _ ≤ (0.000260713533 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12278 BstLean.Part154.csC) ≤ 0.001042922104 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12278 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12278 BstLean.Part154.csC) (piBar (rhoBar 12278 BstLean.Part154.csC)) ≤ 0.000199135080 ∧
    cc1 (rhoBar 12278 BstLean.Part154.csC) (piBar (rhoBar 12278 BstLean.Part154.csC)) ≤ 0.000126710907 ∧
    cc2 (rhoBar 12278 BstLean.Part154.csC) ≤ 0.000073556571 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12278 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12278 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12278 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12278 BstLean.Part154.csC * nuR (rhoBar 12278 BstLean.Part154.csC)) ≤ 0.000521444059 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260713533 : ℝ) * 0.001042922104 := by gcongr
      _ ≤ (0.000521444059 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12278 BstLean.Part154.csC) * nuR (rhoBar 12278 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042922104 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12278 BstLean.Part154.csC) * rhoBar 12278 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260713533 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260713533 / 2 + 0.399 * 0.001042922104 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199135080 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521444059 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126710907 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260713533 / 1.414213562 := by gcongr
      _ ≤ (0.000073556571 : ℝ) := by norm_num

end BstLean.Part264b.N12278

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12278
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12278 BstLean.Part154.csC) (piBar (rhoBar 12278 BstLean.Part154.csC)) ≤ 1.71250E-7 := by
  have hr0 : 0 ≤ rhoBar 12278 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12278 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12278 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12278 BstLean.Part154.csC) (piBar (rhoBar 12278 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12278 BstLean.Part154.csC) (piBar (rhoBar 12278 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12278 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199135080 : ℝ) ^ 2 + 0.000126710907 ^ 2 + 3 * 0.000073556571 ^ 2 +
        2 * 0.797885 * 0.000199135080 * 0.000126710907 + 2 * 0.000199135080 * 0.000073556571 +
        4 * 0.797885 * 0.000126710907 * 0.000073556571 := by gcongr
    _ ≤ (1.71250E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12278 BstLean.Part154.csC Θ ≤ 0.002723533019 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12278 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12278 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12278 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12278 BstLean.Part154.csC) (piBar (rhoBar 12278 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12278 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71250E-7 / (0.000260692975 : ℝ) := by gcongr
    _ ≤ 0.002723533019 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12278 BstLean.Part154.csC Θ ≤ 0.003023699899 + 0.000688137430 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12278 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12278 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12278 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260713533 +
        (6863 / 10000) * 0.000260713533 * 12278 * 0.001042922104) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003023699899 + 0.000688137430 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12278 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12278 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12278 0.011 Θ ∧ gammaRatio 12278 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12278 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12278) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12278 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12278 0.011 Θ) :=
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
    badAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12278 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12278 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12278 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12278 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12278 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12278 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12278 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12278 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12278 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12278 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12278 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004123699899 + 0.003411670449 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12278

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12278
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12278 BstLean.Part154.csC) (piBar (rhoBar 12278 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12278 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12278 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12278 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12278 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12278 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12278 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12278 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12278 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12278 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12278 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12278 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12278 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053388509887 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12278) ≤ 0.010777720560 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12278 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010777720560 + 2 * 0.737676 / 12278) := by gcongr
    _ ≤ (0.053388509887 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12278 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12278

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12278
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483828270 : ℝ) ≤ plow 12278 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12278) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421426885)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429854835) : eMP 12278 0.011 xi bn ≤ 0.001230256241 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12278 : ℝ) * (1 - 0.011))) ≤ 0.000608217588 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001429854835 / (12278 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608217588 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608217588 : ℝ) + 3.141593 * 0.053421426885 / (12278 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001230256241 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421426885)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429854835) : PiBarMP 12278 12 0.011 xi bn ≤ 0.164032776814 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12278 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037813421361 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.195018036207 : ℝ) ≤ √((12278 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.806137014156 : ℝ) ≤ √12278 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12278) ≤ 0.125736792548 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037813421361 + 0.053421426885 * 1.772454 / (2 * (110.195018036207 : ℝ))) * (1 + 0.001230256241) +
        8 / (12278 * 110.806137014156) + 0.125736792548 := by gcongr
    _ ≤ (0.164032776814 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421426885)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429854835) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284519267003) :
    parallelOracle 12278 0.011 xi bn cd ≤ 0.165060243205 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12278 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12278 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483828270 : ℝ) ≤ plow 12278 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.806137014156 : ℝ) ≤ √12278 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284519267003 : ℝ) / (2 * 0.560483828270 * 110.806137014156)) * 0.164032776814 +
        0.284519267003 ^ 2 / (2 * 0.560483828270 * 110.806137014156) := by gcongr
    _ ≤ (0.165060243205 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421426885) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429854835)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284519267003) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12278 12278 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483828270 : ℝ) ≤ plow 12278 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.806137014156 : ℝ) ≤ √12278 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12278 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12278 Θ 1.22 ≤ 0.011967753193 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.806137014156 := by gcongr <;> linarith
      _ ≤ (0.011967753193 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12278 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12278 12278 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12278 12278 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12278 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12278 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12278 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12278 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165060243205 + 0.011967753193 + (0.008646 : ℝ) *
        (1 + 2 * (0.284519267003 + 0.011967753193) / (0.560483828270 * 110.806137014156))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12278]

end BstLean.Part264b.N12278

/-! The original eight local profiles supply actual 12278 moment certificates. -/
namespace BstLean.Part264b.N12278
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12278 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053421426885 ∧
    0 ≤ bN 12278 BstLean.Part154.csC (groupTheta g) ∧ bN 12278 BstLean.Part154.csC (groupTheta g) ≤ 0.001429854835 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12278 12278 0.011
      (momentAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12278 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12278 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12278 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231130757116 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12278 0.011
      (momentAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12278 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12278
/-! The actual computed-centre upper energy formula at 12278. -/
namespace BstLean.Part264b.N12278
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12278

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12278
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12278 cell12278)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086833305477
  | 2 => 0.087803465704
  | 3 => 0.088776187588
  | 4 => 0.089753872731
  | 5 => 0.090739387398
  | 6 => 0.091736126329
  | 7 => 0.092748081623
  | 8 => 0.093779916601
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12278 12278 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12278 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12278

/-! Actual upper energy certificates on all 43 source endpoints at 12278. -/
namespace BstLean.Part264b.N12278
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12278 cell12278)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12278 (gMinus 12278) (1 - (cell12278 i).lower) ≤ 1 ∧
    energyUpper 12278 (gMinus 12278) (BstLean.Part211.gPlus 12278)
      (finiteEnergy 12278 12278 0.011) (1 - (cell12278 i).lower) ≤
      (cell12278 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12278) (by norm_num)
        (q := 1 - (cell12278 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12278,cell12278]) (by norm_num [scalarRow12278,cell12278])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12278,cell12278])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12278

/-! Source-cell containment and simple scalar guards at 12278. -/
namespace BstLean.Part264b.N12278
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12278 cell12278)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12278 ⟨10,by decide⟩).lower ∧ (cell12278 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12278 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12278 ⟨11,by decide⟩).lower ∧ (cell12278 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12278 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12278 ⟨12,by decide⟩).lower ∧ (cell12278 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12278 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12278 ⟨13,by decide⟩).lower ∧ (cell12278 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12278 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12278 ⟨14,by decide⟩).lower ∧ (cell12278 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12278 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12278 ⟨15,by decide⟩).lower ∧ (cell12278 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12278 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12278 ⟨16,by decide⟩).lower ∧ (cell12278 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12278 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12278 ⟨17,by decide⟩).lower ∧ (cell12278 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12278 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12278 ⟨18,by decide⟩).lower ∧ (cell12278 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12278 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12278 ⟨19,by decide⟩).lower ∧ (cell12278 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12278 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12278 ⟨20,by decide⟩).lower ∧ (cell12278 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12278 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12278 ⟨21,by decide⟩).lower ∧ (cell12278 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12278 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12278 ⟨22,by decide⟩).lower ∧ (cell12278 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12278 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12278 ⟨23,by decide⟩).lower ∧ (cell12278 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12278 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12278 ⟨24,by decide⟩).lower ∧ (cell12278 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12278 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12278 ⟨25,by decide⟩).lower ∧ (cell12278 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12278 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12278 ⟨26,by decide⟩).lower ∧ (cell12278 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12278 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12278 ⟨27,by decide⟩).lower ∧ (cell12278 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12278 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12278 ⟨28,by decide⟩).lower ∧ (cell12278 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12278 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12278 ⟨29,by decide⟩).lower ∧ (cell12278 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12278 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12278 ⟨30,by decide⟩).lower ∧ (cell12278 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12278 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12278 ⟨31,by decide⟩).lower ∧ (cell12278 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12278 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12278 ⟨32,by decide⟩).lower ∧ (cell12278 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12278 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12278 ⟨33,by decide⟩).lower ∧ (cell12278 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12278 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12278 ⟨34,by decide⟩).lower ∧ (cell12278 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12278 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12278 ⟨35,by decide⟩).lower ∧ (cell12278 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12278 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12278 ⟨36,by decide⟩).lower ∧ (cell12278 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12278 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12278 ⟨37,by decide⟩).lower ∧ (cell12278 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12278 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12278 ⟨38,by decide⟩).lower ∧ (cell12278 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12278 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12278 ⟨39,by decide⟩).lower ∧ (cell12278 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12278 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12278 ⟨40,by decide⟩).lower ∧ (cell12278 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12278 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12278 ⟨41,by decide⟩).lower ∧ (cell12278 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12278 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12278 ⟨42,by decide⟩).lower ∧ (cell12278 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12278 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12278 ⟨43,by decide⟩).lower ∧ (cell12278 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12278 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12278 ⟨44,by decide⟩).lower ∧ (cell12278 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12278 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12278 ⟨45,by decide⟩).lower ∧ (cell12278 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12278 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12278 ⟨46,by decide⟩).lower ∧ (cell12278 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12278 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12278 ⟨47,by decide⟩).lower ∧ (cell12278 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12278 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12278 ⟨48,by decide⟩).lower ∧ (cell12278 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12278 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12278 ⟨49,by decide⟩).lower ∧ (cell12278 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12278 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12278 ⟨50,by decide⟩).lower ∧ (cell12278 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12278 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12278 ⟨51,by decide⟩).lower ∧ (cell12278 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12278 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12278 ⟨52,by decide⟩).lower ∧ (cell12278 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12278 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12278 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12278 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12278,cell12278,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12278 i).lower ∧
    (cell12278 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12278 i).upper ≤ (0.532 : ℝ) ∧
    (cell12278 i).centre ≤ (0.1 : ℝ) ∧ (cell12278 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12278 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12278 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12278

/-! The local source numeric instances at 12278 have no network premises. -/
namespace BstLean.Part264b.N12278
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12278 cell12278)

noncomputable def sourceNumerics12278 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12278 (cell12278 i)
      scalarRow12278.M scalarRow12278.H scalarRow12278.xi := by
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
    energy_allowance := scalarRow12278.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12278]
    centre_nonneg := (scalarRow12278.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12278]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12278
/-! Actual 12279 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12279
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12279 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12279 12279 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12279.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12279 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12279 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12279 := gPlus_lower 12279
end BstLean.Part264b.N12279

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12279
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036423373013 : ℝ) ≤ wn 12279 := by
  have hn : √(12279 : ℝ) ≤ 110.810649307727 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12279 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.810649307727 ≤ 2 / √12279 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260671367 : ℝ) ≤ rhoBar 12279 BstLean.Part154.csC ∧
    rhoBar 12279 BstLean.Part154.csC ≤ 0.000260692301 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036423373013 : ℝ) / (1.295212 * 12279) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12279) := by gcongr
      _ ≤ (0.000260692301 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12279 BstLean.Part154.csC) ≤ 0.001042837165 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12279 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12279 BstLean.Part154.csC) (piBar (rhoBar 12279 BstLean.Part154.csC)) ≤ 0.000199118862 ∧
    cc1 (rhoBar 12279 BstLean.Part154.csC) (piBar (rhoBar 12279 BstLean.Part154.csC)) ≤ 0.000126700587 ∧
    cc2 (rhoBar 12279 BstLean.Part154.csC) ≤ 0.000073550581 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12279 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12279 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12279 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12279 BstLean.Part154.csC * nuR (rhoBar 12279 BstLean.Part154.csC)) ≤ 0.000521401592 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260692301 : ℝ) * 0.001042837165 := by gcongr
      _ ≤ (0.000521401592 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12279 BstLean.Part154.csC) * nuR (rhoBar 12279 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042837165 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12279 BstLean.Part154.csC) * rhoBar 12279 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260692301 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260692301 / 2 + 0.399 * 0.001042837165 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199118862 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521401592 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126700587 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260692301 / 1.414213562 := by gcongr
      _ ≤ (0.000073550581 : ℝ) := by norm_num

end BstLean.Part264b.N12279

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12279
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12279 BstLean.Part154.csC) (piBar (rhoBar 12279 BstLean.Part154.csC)) ≤ 1.71222E-7 := by
  have hr0 : 0 ≤ rhoBar 12279 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12279 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12279 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12279 BstLean.Part154.csC) (piBar (rhoBar 12279 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12279 BstLean.Part154.csC) (piBar (rhoBar 12279 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12279 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199118862 : ℝ) ^ 2 + 0.000126700587 ^ 2 + 3 * 0.000073550581 ^ 2 +
        2 * 0.797885 * 0.000199118862 * 0.000126700587 + 2 * 0.000199118862 * 0.000073550581 +
        4 * 0.797885 * 0.000126700587 * 0.000073550581 := by gcongr
    _ ≤ (1.71222E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12279 BstLean.Part154.csC Θ ≤ 0.002723313438 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12279 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12279 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12279 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12279 BstLean.Part154.csC) (piBar (rhoBar 12279 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12279 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71222E-7 / (0.000260671367 : ℝ) := by gcongr
    _ ≤ 0.002723313438 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12279 BstLean.Part154.csC Θ ≤ 0.003023453645 + 0.000688081390 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12279 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12279 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12279 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260692301 +
        (6863 / 10000) * 0.000260692301 * 12279 * 0.001042837165) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003023453645 + 0.000688081390 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12279 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12279 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12279 0.011 Θ ∧ gammaRatio 12279 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12279 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12279) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12279 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12279 0.011 Θ) :=
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
    badAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12279 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12279 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12279 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12279 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12279 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12279 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12279 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12279 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12279 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12279 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12279 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004123453645 + 0.003411394828 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12279

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12279
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12279 BstLean.Part154.csC) (piBar (rhoBar 12279 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12279 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12279 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12279 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12279 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12279 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12279 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12279 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12279 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12279 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12279 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12279 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12279 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053386311896 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12279) ≤ 0.010777281683 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12279 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010777281683 + 2 * 0.737676 / 12279) := by gcongr
    _ ≤ (0.053386311896 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12279 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12279

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12279
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483876651 : ℝ) ≤ plow 12279 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12279) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421035930)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429739555) : eMP 12279 0.011 xi bn ≤ 0.001230156444 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12279 : ℝ) * (1 - 0.011))) ≤ 0.000608168303 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001429739555 / (12279 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608168303 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608168303 : ℝ) + 3.141593 * 0.053421035930 / (12279 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001230156444 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421035930)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429739555) : PiBarMP 12279 12 0.011 xi bn ≤ 0.164026105285 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12279 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037811897004 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.199505443536 : ℝ) ≤ √((12279 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.810649307726 : ℝ) ≤ √12279 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12279) ≤ 0.125731672451 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037811897004 + 0.053421035930 * 1.772454 / (2 * (110.199505443536 : ℝ))) * (1 + 0.001230156444) +
        8 / (12279 * 110.810649307726) + 0.125731672451 := by gcongr
    _ ≤ (0.164026105285 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421035930)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429739555) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284516223267) :
    parallelOracle 12279 0.011 xi bn cd ≤ 0.165053496504 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12279 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12279 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483876651 : ℝ) ≤ plow 12279 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.810649307726 : ℝ) ≤ √12279 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284516223267 : ℝ) / (2 * 0.560483876651 * 110.810649307726)) * 0.164026105285 +
        0.284516223267 ^ 2 / (2 * 0.560483876651 * 110.810649307726) := by gcongr
    _ ≤ (0.165053496504 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053421035930) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429739555)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284516223267) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12279 12279 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483876651 : ℝ) ≤ plow 12279 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.810649307726 : ℝ) ≤ √12279 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12279 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12279 Θ 1.22 ≤ 0.011967265857 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.810649307726 := by gcongr <;> linarith
      _ ≤ (0.011967265857 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12279 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12279 12279 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12279 12279 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12279 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12279 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12279 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12279 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165053496504 + 0.011967265857 + (0.008646 : ℝ) *
        (1 + 2 * (0.284516223267 + 0.011967265857) / (0.560483876651 * 110.810649307726))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12279]

end BstLean.Part264b.N12279

/-! The original eight local profiles supply actual 12279 moment certificates. -/
namespace BstLean.Part264b.N12279
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12279 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053421035930 ∧
    0 ≤ bN 12279 BstLean.Part154.csC (groupTheta g) ∧ bN 12279 BstLean.Part154.csC (groupTheta g) ≤ 0.001429739555 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12279 12279 0.011
      (momentAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12279 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12279 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12279 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231129911371 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12279 0.011
      (momentAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12279 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12279
/-! The actual computed-centre upper energy formula at 12279. -/
namespace BstLean.Part264b.N12279
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12279

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12279
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12279 cell12279)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086829814290
  | 2 => 0.087799895925
  | 3 => 0.088772525565
  | 4 => 0.089750101858
  | 5 => 0.090735487636
  | 6 => 0.091732073657
  | 7 => 0.092743847447
  | 8 => 0.093775467095
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12279 12279 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12279 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12279

/-! Actual upper energy certificates on all 43 source endpoints at 12279. -/
namespace BstLean.Part264b.N12279
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12279 cell12279)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12279 (gMinus 12279) (1 - (cell12279 i).lower) ≤ 1 ∧
    energyUpper 12279 (gMinus 12279) (BstLean.Part211.gPlus 12279)
      (finiteEnergy 12279 12279 0.011) (1 - (cell12279 i).lower) ≤
      (cell12279 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12279) (by norm_num)
        (q := 1 - (cell12279 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12279,cell12279]) (by norm_num [scalarRow12279,cell12279])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12279,cell12279])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12279

/-! Source-cell containment and simple scalar guards at 12279. -/
namespace BstLean.Part264b.N12279
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12279 cell12279)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12279 ⟨10,by decide⟩).lower ∧ (cell12279 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12279 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12279 ⟨11,by decide⟩).lower ∧ (cell12279 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12279 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12279 ⟨12,by decide⟩).lower ∧ (cell12279 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12279 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12279 ⟨13,by decide⟩).lower ∧ (cell12279 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12279 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12279 ⟨14,by decide⟩).lower ∧ (cell12279 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12279 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12279 ⟨15,by decide⟩).lower ∧ (cell12279 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12279 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12279 ⟨16,by decide⟩).lower ∧ (cell12279 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12279 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12279 ⟨17,by decide⟩).lower ∧ (cell12279 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12279 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12279 ⟨18,by decide⟩).lower ∧ (cell12279 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12279 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12279 ⟨19,by decide⟩).lower ∧ (cell12279 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12279 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12279 ⟨20,by decide⟩).lower ∧ (cell12279 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12279 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12279 ⟨21,by decide⟩).lower ∧ (cell12279 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12279 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12279 ⟨22,by decide⟩).lower ∧ (cell12279 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12279 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12279 ⟨23,by decide⟩).lower ∧ (cell12279 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12279 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12279 ⟨24,by decide⟩).lower ∧ (cell12279 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12279 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12279 ⟨25,by decide⟩).lower ∧ (cell12279 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12279 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12279 ⟨26,by decide⟩).lower ∧ (cell12279 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12279 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12279 ⟨27,by decide⟩).lower ∧ (cell12279 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12279 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12279 ⟨28,by decide⟩).lower ∧ (cell12279 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12279 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12279 ⟨29,by decide⟩).lower ∧ (cell12279 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12279 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12279 ⟨30,by decide⟩).lower ∧ (cell12279 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12279 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12279 ⟨31,by decide⟩).lower ∧ (cell12279 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12279 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12279 ⟨32,by decide⟩).lower ∧ (cell12279 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12279 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12279 ⟨33,by decide⟩).lower ∧ (cell12279 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12279 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12279 ⟨34,by decide⟩).lower ∧ (cell12279 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12279 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12279 ⟨35,by decide⟩).lower ∧ (cell12279 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12279 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12279 ⟨36,by decide⟩).lower ∧ (cell12279 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12279 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12279 ⟨37,by decide⟩).lower ∧ (cell12279 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12279 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12279 ⟨38,by decide⟩).lower ∧ (cell12279 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12279 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12279 ⟨39,by decide⟩).lower ∧ (cell12279 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12279 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12279 ⟨40,by decide⟩).lower ∧ (cell12279 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12279 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12279 ⟨41,by decide⟩).lower ∧ (cell12279 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12279 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12279 ⟨42,by decide⟩).lower ∧ (cell12279 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12279 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12279 ⟨43,by decide⟩).lower ∧ (cell12279 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12279 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12279 ⟨44,by decide⟩).lower ∧ (cell12279 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12279 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12279 ⟨45,by decide⟩).lower ∧ (cell12279 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12279 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12279 ⟨46,by decide⟩).lower ∧ (cell12279 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12279 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12279 ⟨47,by decide⟩).lower ∧ (cell12279 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12279 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12279 ⟨48,by decide⟩).lower ∧ (cell12279 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12279 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12279 ⟨49,by decide⟩).lower ∧ (cell12279 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12279 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12279 ⟨50,by decide⟩).lower ∧ (cell12279 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12279 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12279 ⟨51,by decide⟩).lower ∧ (cell12279 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12279 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12279 ⟨52,by decide⟩).lower ∧ (cell12279 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12279 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12279 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12279 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12279,cell12279,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12279 i).lower ∧
    (cell12279 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12279 i).upper ≤ (0.532 : ℝ) ∧
    (cell12279 i).centre ≤ (0.1 : ℝ) ∧ (cell12279 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12279 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12279 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12279

/-! The local source numeric instances at 12279 have no network premises. -/
namespace BstLean.Part264b.N12279
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12279 cell12279)

noncomputable def sourceNumerics12279 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12279 (cell12279 i)
      scalarRow12279.M scalarRow12279.H scalarRow12279.xi := by
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
    energy_allowance := scalarRow12279.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12279]
    centre_nonneg := (scalarRow12279.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12279]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12279
/-! Actual 12280 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12280
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12280 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12280 12280 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12280.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12280 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12280 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12280 := gPlus_lower 12280
end BstLean.Part264b.N12280

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12280
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036421876683 : ℝ) ≤ wn 12280 := by
  have hn : √(12280 : ℝ) ≤ 110.815161417561 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12280 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.815161417561 ≤ 2 / √12280 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260649764 : ℝ) ≤ rhoBar 12280 BstLean.Part154.csC ∧
    rhoBar 12280 BstLean.Part154.csC ≤ 0.000260671072 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036421876683 : ℝ) / (1.295212 * 12280) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12280) := by gcongr
      _ ≤ (0.000260671072 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12280 BstLean.Part154.csC) ≤ 0.001042752238 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12280 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12280 BstLean.Part154.csC) (piBar (rhoBar 12280 BstLean.Part154.csC)) ≤ 0.000199102647 ∧
    cc1 (rhoBar 12280 BstLean.Part154.csC) (piBar (rhoBar 12280 BstLean.Part154.csC)) ≤ 0.000126690270 ∧
    cc2 (rhoBar 12280 BstLean.Part154.csC) ≤ 0.000073544591 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12280 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12280 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12280 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12280 BstLean.Part154.csC * nuR (rhoBar 12280 BstLean.Part154.csC)) ≤ 0.000521359132 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260671072 : ℝ) * 0.001042752238 := by gcongr
      _ ≤ (0.000521359132 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12280 BstLean.Part154.csC) * nuR (rhoBar 12280 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042752238 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12280 BstLean.Part154.csC) * rhoBar 12280 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260671072 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260671072 / 2 + 0.399 * 0.001042752238 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199102647 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521359132 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126690270 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260671072 / 1.414213562 := by gcongr
      _ ≤ (0.000073544591 : ℝ) := by norm_num

end BstLean.Part264b.N12280

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12280
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12280 BstLean.Part154.csC) (piBar (rhoBar 12280 BstLean.Part154.csC)) ≤ 1.71194E-7 := by
  have hr0 : 0 ≤ rhoBar 12280 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12280 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12280 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12280 BstLean.Part154.csC) (piBar (rhoBar 12280 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12280 BstLean.Part154.csC) (piBar (rhoBar 12280 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12280 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199102647 : ℝ) ^ 2 + 0.000126690270 ^ 2 + 3 * 0.000073544591 ^ 2 +
        2 * 0.797885 * 0.000199102647 * 0.000126690270 + 2 * 0.000199102647 * 0.000073544591 +
        4 * 0.797885 * 0.000126690270 * 0.000073544591 := by gcongr
    _ ≤ (1.71194E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12280 BstLean.Part154.csC Θ ≤ 0.002723093768 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12280 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12280 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12280 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12280 BstLean.Part154.csC) (piBar (rhoBar 12280 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12280 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71194E-7 / (0.000260649764 : ℝ) := by gcongr
    _ ≤ 0.002723093768 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12280 BstLean.Part154.csC Θ ≤ 0.003023207420 + 0.000688025357 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12280 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12280 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12280 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260671072 +
        (6863 / 10000) * 0.000260671072 * 12280 * 0.001042752238) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003023207420 + 0.000688025357 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12280 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12280 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12280 0.011 Θ ∧ gammaRatio 12280 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12280 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12280) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12280 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12280 0.011 Θ) :=
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
    badAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12280 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12280 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12280 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12280 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12280 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12280 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12280 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12280 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12280 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12280 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12280 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004123207420 + 0.003411119125 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12280

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12280
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12280 BstLean.Part154.csC) (piBar (rhoBar 12280 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12280 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12280 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12280 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12280 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12280 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12280 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12280 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12280 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12280 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12280 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12280 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12280 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053384114177 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12280) ≤ 0.010776842860 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12280 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010776842860 + 2 * 0.737676 / 12280) := by gcongr
    _ ≤ (0.053384114177 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12280 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12280

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12280
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483925024 : ℝ) ≤ plow 12280 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12280) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053420644961)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429624229) : eMP 12280 0.011 xi bn ≤ 0.001230056635 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12280 : ℝ) * (1 - 0.011))) ≤ 0.000608119012 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001429624229 / (12280 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608119012 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608119012 : ℝ) + 3.141593 * 0.053420644961 / (12280 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001230056635 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053420644961)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429624229) : PiBarMP 12280 12 0.011 xi bn ≤ 0.164019433713 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12280 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037810371977 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.203992668142 : ℝ) ≤ √((12280 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.815161417560 : ℝ) ≤ √12280 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12280) ≤ 0.125726552979 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037810371977 + 0.053420644961 * 1.772454 / (2 * (110.203992668142 : ℝ))) * (1 + 0.001230056635) +
        8 / (12280 * 110.815161417560) + 0.125726552979 := by gcongr
    _ ≤ (0.164019433713 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053420644961)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429624229) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284513179769) :
    parallelOracle 12280 0.011 xi bn cd ≤ 0.165046749769 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12280 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12280 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483925024 : ℝ) ≤ plow 12280 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.815161417560 : ℝ) ≤ √12280 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284513179769 : ℝ) / (2 * 0.560483925024 * 110.815161417560)) * 0.164019433713 +
        0.284513179769 ^ 2 / (2 * 0.560483925024 * 110.815161417560) := by gcongr
    _ ≤ (0.165046749769 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053420644961) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429624229)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284513179769) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12280 12280 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483925024 : ℝ) ≤ plow 12280 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.815161417560 : ℝ) ≤ √12280 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12280 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12280 Θ 1.22 ≤ 0.011966778581 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.815161417560 := by gcongr <;> linarith
      _ ≤ (0.011966778581 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12280 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12280 12280 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12280 12280 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12280 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12280 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12280 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12280 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165046749769 + 0.011966778581 + (0.008646 : ℝ) *
        (1 + 2 * (0.284513179769 + 0.011966778581) / (0.560483925024 * 110.815161417560))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12280]

end BstLean.Part264b.N12280

/-! The original eight local profiles supply actual 12280 moment certificates. -/
namespace BstLean.Part264b.N12280
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12280 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053420644961 ∧
    0 ≤ bN 12280 BstLean.Part154.csC (groupTheta g) ∧ bN 12280 BstLean.Part154.csC (groupTheta g) ≤ 0.001429624229 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12280 12280 0.011
      (momentAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12280 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12280 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12280 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231129065592 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12280 0.011
      (momentAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12280 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12280
/-! The actual computed-centre upper energy formula at 12280. -/
namespace BstLean.Part264b.N12280
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12280

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12280
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12280 cell12280)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086826324801
  | 2 => 0.087796327922
  | 3 => 0.088768865412
  | 4 => 0.089746332974
  | 5 => 0.090731590003
  | 6 => 0.091728023287
  | 7 => 0.092739615778
  | 8 => 0.093771020342
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12280 12280 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12280 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12280

/-! Actual upper energy certificates on all 43 source endpoints at 12280. -/
namespace BstLean.Part264b.N12280
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12280 cell12280)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12280 (gMinus 12280) (1 - (cell12280 i).lower) ≤ 1 ∧
    energyUpper 12280 (gMinus 12280) (BstLean.Part211.gPlus 12280)
      (finiteEnergy 12280 12280 0.011) (1 - (cell12280 i).lower) ≤
      (cell12280 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12280) (by norm_num)
        (q := 1 - (cell12280 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12280,cell12280]) (by norm_num [scalarRow12280,cell12280])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12280,cell12280])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12280

/-! Source-cell containment and simple scalar guards at 12280. -/
namespace BstLean.Part264b.N12280
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12280 cell12280)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12280 ⟨10,by decide⟩).lower ∧ (cell12280 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12280 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12280 ⟨11,by decide⟩).lower ∧ (cell12280 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12280 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12280 ⟨12,by decide⟩).lower ∧ (cell12280 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12280 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12280 ⟨13,by decide⟩).lower ∧ (cell12280 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12280 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12280 ⟨14,by decide⟩).lower ∧ (cell12280 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12280 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12280 ⟨15,by decide⟩).lower ∧ (cell12280 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12280 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12280 ⟨16,by decide⟩).lower ∧ (cell12280 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12280 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12280 ⟨17,by decide⟩).lower ∧ (cell12280 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12280 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12280 ⟨18,by decide⟩).lower ∧ (cell12280 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12280 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12280 ⟨19,by decide⟩).lower ∧ (cell12280 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12280 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12280 ⟨20,by decide⟩).lower ∧ (cell12280 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12280 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12280 ⟨21,by decide⟩).lower ∧ (cell12280 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12280 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12280 ⟨22,by decide⟩).lower ∧ (cell12280 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12280 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12280 ⟨23,by decide⟩).lower ∧ (cell12280 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12280 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12280 ⟨24,by decide⟩).lower ∧ (cell12280 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12280 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12280 ⟨25,by decide⟩).lower ∧ (cell12280 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12280 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12280 ⟨26,by decide⟩).lower ∧ (cell12280 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12280 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12280 ⟨27,by decide⟩).lower ∧ (cell12280 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12280 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12280 ⟨28,by decide⟩).lower ∧ (cell12280 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12280 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12280 ⟨29,by decide⟩).lower ∧ (cell12280 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12280 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12280 ⟨30,by decide⟩).lower ∧ (cell12280 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12280 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12280 ⟨31,by decide⟩).lower ∧ (cell12280 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12280 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12280 ⟨32,by decide⟩).lower ∧ (cell12280 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12280 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12280 ⟨33,by decide⟩).lower ∧ (cell12280 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12280 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12280 ⟨34,by decide⟩).lower ∧ (cell12280 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12280 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12280 ⟨35,by decide⟩).lower ∧ (cell12280 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12280 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12280 ⟨36,by decide⟩).lower ∧ (cell12280 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12280 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12280 ⟨37,by decide⟩).lower ∧ (cell12280 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12280 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12280 ⟨38,by decide⟩).lower ∧ (cell12280 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12280 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12280 ⟨39,by decide⟩).lower ∧ (cell12280 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12280 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12280 ⟨40,by decide⟩).lower ∧ (cell12280 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12280 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12280 ⟨41,by decide⟩).lower ∧ (cell12280 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12280 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12280 ⟨42,by decide⟩).lower ∧ (cell12280 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12280 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12280 ⟨43,by decide⟩).lower ∧ (cell12280 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12280 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12280 ⟨44,by decide⟩).lower ∧ (cell12280 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12280 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12280 ⟨45,by decide⟩).lower ∧ (cell12280 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12280 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12280 ⟨46,by decide⟩).lower ∧ (cell12280 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12280 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12280 ⟨47,by decide⟩).lower ∧ (cell12280 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12280 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12280 ⟨48,by decide⟩).lower ∧ (cell12280 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12280 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12280 ⟨49,by decide⟩).lower ∧ (cell12280 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12280 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12280 ⟨50,by decide⟩).lower ∧ (cell12280 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12280 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12280 ⟨51,by decide⟩).lower ∧ (cell12280 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12280 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12280 ⟨52,by decide⟩).lower ∧ (cell12280 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12280 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12280 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12280 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12280,cell12280,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12280 i).lower ∧
    (cell12280 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12280 i).upper ≤ (0.532 : ℝ) ∧
    (cell12280 i).centre ≤ (0.1 : ℝ) ∧ (cell12280 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12280 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12280 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12280

/-! The local source numeric instances at 12280 have no network premises. -/
namespace BstLean.Part264b.N12280
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12280 cell12280)

noncomputable def sourceNumerics12280 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12280 (cell12280 i)
      scalarRow12280.M scalarRow12280.H scalarRow12280.xi := by
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
    energy_allowance := scalarRow12280.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12280]
    centre_nonneg := (scalarRow12280.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12280]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12280
/-! Actual 12281 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12281
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12281 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12281 12281 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12281.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12281 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12281 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12281 := gPlus_lower 12281
end BstLean.Part264b.N12281

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12281
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036420380536 : ℝ) ≤ wn 12281 := by
  have hn : √(12281 : ℝ) ≤ 110.819673343681 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12281 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.819673343681 ≤ 2 / √12281 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260628164 : ℝ) ≤ rhoBar 12281 BstLean.Part154.csC ∧
    rhoBar 12281 BstLean.Part154.csC ≤ 0.000260649846 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036420380536 : ℝ) / (1.295212 * 12281) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12281) := by gcongr
      _ ≤ (0.000260649846 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12281 BstLean.Part154.csC) ≤ 0.001042667323 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12281 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12281 BstLean.Part154.csC) (piBar (rhoBar 12281 BstLean.Part154.csC)) ≤ 0.000199086433 ∧
    cc1 (rhoBar 12281 BstLean.Part154.csC) (piBar (rhoBar 12281 BstLean.Part154.csC)) ≤ 0.000126679953 ∧
    cc2 (rhoBar 12281 BstLean.Part154.csC) ≤ 0.000073538603 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12281 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12281 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12281 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12281 BstLean.Part154.csC * nuR (rhoBar 12281 BstLean.Part154.csC)) ≤ 0.000521316677 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260649846 : ℝ) * 0.001042667323 := by gcongr
      _ ≤ (0.000521316677 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12281 BstLean.Part154.csC) * nuR (rhoBar 12281 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042667323 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12281 BstLean.Part154.csC) * rhoBar 12281 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260649846 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260649846 / 2 + 0.399 * 0.001042667323 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199086433 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521316677 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126679953 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260649846 / 1.414213562 := by gcongr
      _ ≤ (0.000073538603 : ℝ) := by norm_num

end BstLean.Part264b.N12281

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12281
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12281 BstLean.Part154.csC) (piBar (rhoBar 12281 BstLean.Part154.csC)) ≤ 1.71166E-7 := by
  have hr0 : 0 ≤ rhoBar 12281 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12281 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12281 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12281 BstLean.Part154.csC) (piBar (rhoBar 12281 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12281 BstLean.Part154.csC) (piBar (rhoBar 12281 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12281 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199086433 : ℝ) ^ 2 + 0.000126679953 ^ 2 + 3 * 0.000073538603 ^ 2 +
        2 * 0.797885 * 0.000199086433 * 0.000126679953 + 2 * 0.000199086433 * 0.000073538603 +
        4 * 0.797885 * 0.000126679953 * 0.000073538603 := by gcongr
    _ ≤ (1.71166E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12281 BstLean.Part154.csC Θ ≤ 0.002722874031 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12281 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12281 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12281 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12281 BstLean.Part154.csC) (piBar (rhoBar 12281 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12281 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71166E-7 / (0.000260628164 : ℝ) := by gcongr
    _ ≤ 0.002722874031 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12281 BstLean.Part154.csC Θ ≤ 0.003022961224 + 0.000687969332 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12281 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12281 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12281 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260649846 +
        (6863 / 10000) * 0.000260649846 * 12281 * 0.001042667323) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003022961224 + 0.000687969332 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12281 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12281 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12281 0.011 Θ ∧ gammaRatio 12281 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12281 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12281) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12281 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12281 0.011 Θ) :=
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
    badAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12281 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12281 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12281 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12281 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12281 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12281 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12281 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12281 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12281 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12281 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12281 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004122961224 + 0.003410843363 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12281

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12281
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12281 BstLean.Part154.csC) (piBar (rhoBar 12281 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12281 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12281 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12281 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12281 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12281 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12281 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12281 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12281 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12281 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12281 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12281 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12281 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053381916726 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12281) ≤ 0.010776404090 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12281 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010776404090 + 2 * 0.737676 / 12281) := by gcongr
    _ ≤ (0.053381916726 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12281 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12281

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12281
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483973389 : ℝ) ≤ plow 12281 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12281) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053420253990)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429508867) : eMP 12281 0.011 xi bn ≤ 0.001229956821 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12281 : ℝ) * (1 - 0.011))) ≤ 0.000608069718 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001429508867 / (12281 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608069718 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608069718 : ℝ) + 3.141593 * 0.053420253990 / (12281 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001229956821 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053420253990)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429508867) : PiBarMP 12281 12 0.011 xi bn ≤ 0.164012762230 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12281 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037808846412 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.208479710047 : ℝ) ≤ √((12281 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.819673343680 : ℝ) ≤ √12281 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12281) ≤ 0.125721434132 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037808846412 + 0.053420253990 * 1.772454 / (2 * (110.208479710047 : ℝ))) * (1 + 0.001229956821) +
        8 / (12281 * 110.819673343680) + 0.125721434132 := by gcongr
    _ ≤ (0.164012762230 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053420253990)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429508867) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284510136531) :
    parallelOracle 12281 0.011 xi bn cd ≤ 0.165040003134 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12281 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12281 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483973389 : ℝ) ≤ plow 12281 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.819673343680 : ℝ) ≤ √12281 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284510136531 : ℝ) / (2 * 0.560483973389 * 110.819673343680)) * 0.164012762230 +
        0.284510136531 ^ 2 / (2 * 0.560483973389 * 110.819673343680) := by gcongr
    _ ≤ (0.165040003134 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053420253990) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429508867)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284510136531) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12281 12281 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483973389 : ℝ) ≤ plow 12281 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.819673343680 : ℝ) ≤ √12281 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12281 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12281 Θ 1.22 ≤ 0.011966291364 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.819673343680 := by gcongr <;> linarith
      _ ≤ (0.011966291364 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12281 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12281 12281 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12281 12281 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12281 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12281 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12281 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12281 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165040003134 + 0.011966291364 + (0.008646 : ℝ) *
        (1 + 2 * (0.284510136531 + 0.011966291364) / (0.560483973389 * 110.819673343680))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12281]

end BstLean.Part264b.N12281

/-! The original eight local profiles supply actual 12281 moment certificates. -/
namespace BstLean.Part264b.N12281
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12281 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053420253990 ∧
    0 ≤ bN 12281 BstLean.Part154.csC (groupTheta g) ∧ bN 12281 BstLean.Part154.csC (groupTheta g) ≤ 0.001429508867 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12281 12281 0.011
      (momentAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12281 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12281 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12281 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231128219805 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12281 0.011
      (momentAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12281 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12281
/-! The actual computed-centre upper energy formula at 12281. -/
namespace BstLean.Part264b.N12281
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12281

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12281
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12281 cell12281)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086822837009
  | 2 => 0.087792761693
  | 3 => 0.088765207129
  | 4 => 0.089742566075
  | 5 => 0.090727694497
  | 6 => 0.091723975214
  | 7 => 0.092735386612
  | 8 => 0.093766576339
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12281 12281 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12281 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12281

/-! Actual upper energy certificates on all 43 source endpoints at 12281. -/
namespace BstLean.Part264b.N12281
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12281 cell12281)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12281 (gMinus 12281) (1 - (cell12281 i).lower) ≤ 1 ∧
    energyUpper 12281 (gMinus 12281) (BstLean.Part211.gPlus 12281)
      (finiteEnergy 12281 12281 0.011) (1 - (cell12281 i).lower) ≤
      (cell12281 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12281) (by norm_num)
        (q := 1 - (cell12281 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12281,cell12281]) (by norm_num [scalarRow12281,cell12281])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12281,cell12281])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12281

/-! Source-cell containment and simple scalar guards at 12281. -/
namespace BstLean.Part264b.N12281
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12281 cell12281)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12281 ⟨10,by decide⟩).lower ∧ (cell12281 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12281 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12281 ⟨11,by decide⟩).lower ∧ (cell12281 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12281 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12281 ⟨12,by decide⟩).lower ∧ (cell12281 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12281 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12281 ⟨13,by decide⟩).lower ∧ (cell12281 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12281 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12281 ⟨14,by decide⟩).lower ∧ (cell12281 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12281 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12281 ⟨15,by decide⟩).lower ∧ (cell12281 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12281 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12281 ⟨16,by decide⟩).lower ∧ (cell12281 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12281 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12281 ⟨17,by decide⟩).lower ∧ (cell12281 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12281 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12281 ⟨18,by decide⟩).lower ∧ (cell12281 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12281 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12281 ⟨19,by decide⟩).lower ∧ (cell12281 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12281 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12281 ⟨20,by decide⟩).lower ∧ (cell12281 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12281 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12281 ⟨21,by decide⟩).lower ∧ (cell12281 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12281 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12281 ⟨22,by decide⟩).lower ∧ (cell12281 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12281 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12281 ⟨23,by decide⟩).lower ∧ (cell12281 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12281 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12281 ⟨24,by decide⟩).lower ∧ (cell12281 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12281 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12281 ⟨25,by decide⟩).lower ∧ (cell12281 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12281 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12281 ⟨26,by decide⟩).lower ∧ (cell12281 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12281 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12281 ⟨27,by decide⟩).lower ∧ (cell12281 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12281 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12281 ⟨28,by decide⟩).lower ∧ (cell12281 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12281 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12281 ⟨29,by decide⟩).lower ∧ (cell12281 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12281 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12281 ⟨30,by decide⟩).lower ∧ (cell12281 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12281 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12281 ⟨31,by decide⟩).lower ∧ (cell12281 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12281 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12281 ⟨32,by decide⟩).lower ∧ (cell12281 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12281 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12281 ⟨33,by decide⟩).lower ∧ (cell12281 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12281 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12281 ⟨34,by decide⟩).lower ∧ (cell12281 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12281 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12281 ⟨35,by decide⟩).lower ∧ (cell12281 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12281 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12281 ⟨36,by decide⟩).lower ∧ (cell12281 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12281 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12281 ⟨37,by decide⟩).lower ∧ (cell12281 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12281 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12281 ⟨38,by decide⟩).lower ∧ (cell12281 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12281 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12281 ⟨39,by decide⟩).lower ∧ (cell12281 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12281 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12281 ⟨40,by decide⟩).lower ∧ (cell12281 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12281 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12281 ⟨41,by decide⟩).lower ∧ (cell12281 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12281 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12281 ⟨42,by decide⟩).lower ∧ (cell12281 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12281 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12281 ⟨43,by decide⟩).lower ∧ (cell12281 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12281 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12281 ⟨44,by decide⟩).lower ∧ (cell12281 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12281 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12281 ⟨45,by decide⟩).lower ∧ (cell12281 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12281 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12281 ⟨46,by decide⟩).lower ∧ (cell12281 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12281 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12281 ⟨47,by decide⟩).lower ∧ (cell12281 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12281 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12281 ⟨48,by decide⟩).lower ∧ (cell12281 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12281 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12281 ⟨49,by decide⟩).lower ∧ (cell12281 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12281 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12281 ⟨50,by decide⟩).lower ∧ (cell12281 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12281 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12281 ⟨51,by decide⟩).lower ∧ (cell12281 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12281 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12281 ⟨52,by decide⟩).lower ∧ (cell12281 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12281 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12281 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12281 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12281,cell12281,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12281 i).lower ∧
    (cell12281 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12281 i).upper ≤ (0.532 : ℝ) ∧
    (cell12281 i).centre ≤ (0.1 : ℝ) ∧ (cell12281 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12281 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12281 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12281

/-! The local source numeric instances at 12281 have no network premises. -/
namespace BstLean.Part264b.N12281
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12281 cell12281)

noncomputable def sourceNumerics12281 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12281 (cell12281 i)
      scalarRow12281.M scalarRow12281.H scalarRow12281.xi := by
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
    energy_allowance := scalarRow12281.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12281]
    centre_nonneg := (scalarRow12281.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12281]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12281
/-! Actual 12282 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12282
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12282 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12282 12282 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12282.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12282 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12282 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12282 := gPlus_lower 12282
end BstLean.Part264b.N12282

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12282
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036418884574 : ℝ) ≤ wn 12282 := by
  have hn : √(12282 : ℝ) ≤ 110.824185086109 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12282 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.824185086109 ≤ 2 / √12282 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260606567 : ℝ) ≤ rhoBar 12282 BstLean.Part154.csC ∧
    rhoBar 12282 BstLean.Part154.csC ≤ 0.000260628624 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036418884574 : ℝ) / (1.295212 * 12282) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12282) := by gcongr
      _ ≤ (0.000260628624 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12282 BstLean.Part154.csC) ≤ 0.001042582424 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12282 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12282 BstLean.Part154.csC) (piBar (rhoBar 12282 BstLean.Part154.csC)) ≤ 0.000199070223 ∧
    cc1 (rhoBar 12282 BstLean.Part154.csC) (piBar (rhoBar 12282 BstLean.Part154.csC)) ≤ 0.000126669638 ∧
    cc2 (rhoBar 12282 BstLean.Part154.csC) ≤ 0.000073532615 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12282 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12282 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12282 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12282 BstLean.Part154.csC * nuR (rhoBar 12282 BstLean.Part154.csC)) ≤ 0.000521274230 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260628624 : ℝ) * 0.001042582424 := by gcongr
      _ ≤ (0.000521274230 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12282 BstLean.Part154.csC) * nuR (rhoBar 12282 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042582424 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12282 BstLean.Part154.csC) * rhoBar 12282 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260628624 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260628624 / 2 + 0.399 * 0.001042582424 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199070223 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521274230 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126669638 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260628624 / 1.414213562 := by gcongr
      _ ≤ (0.000073532615 : ℝ) := by norm_num

end BstLean.Part264b.N12282

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12282
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12282 BstLean.Part154.csC) (piBar (rhoBar 12282 BstLean.Part154.csC)) ≤ 1.71138E-7 := by
  have hr0 : 0 ≤ rhoBar 12282 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12282 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12282 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12282 BstLean.Part154.csC) (piBar (rhoBar 12282 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12282 BstLean.Part154.csC) (piBar (rhoBar 12282 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12282 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199070223 : ℝ) ^ 2 + 0.000126669638 ^ 2 + 3 * 0.000073532615 ^ 2 +
        2 * 0.797885 * 0.000199070223 * 0.000126669638 + 2 * 0.000199070223 * 0.000073532615 +
        4 * 0.797885 * 0.000126669638 * 0.000073532615 := by gcongr
    _ ≤ (1.71138E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12282 BstLean.Part154.csC Θ ≤ 0.002722654226 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12282 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12282 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12282 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12282 BstLean.Part154.csC) (piBar (rhoBar 12282 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12282 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71138E-7 / (0.000260606567 : ℝ) := by gcongr
    _ ≤ 0.002722654226 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12282 BstLean.Part154.csC Θ ≤ 0.003022715081 + 0.000687913318 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12282 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12282 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12282 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260628624 +
        (6863 / 10000) * 0.000260628624 * 12282 * 0.001042582424) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003022715081 + 0.000687913318 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12282 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12282 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12282 0.011 Θ ∧ gammaRatio 12282 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12282 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12282) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12282 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12282 0.011 Θ) :=
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
    badAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12282 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12282 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12282 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12282 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12282 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12282 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12282 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12282 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12282 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12282 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12282 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004122715081 + 0.003410567544 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12282

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12282
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12282 BstLean.Part154.csC) (piBar (rhoBar 12282 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12282 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12282 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12282 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12282 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12282 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12282 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12282 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12282 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12282 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12282 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12282 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12282 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053379719547 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12282) ≤ 0.010775965374 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12282 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010775965374 + 2 * 0.737676 / 12282) := by gcongr
    _ ≤ (0.053379719547 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12282 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12282

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12282
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484021747 : ℝ) ≤ plow 12282 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12282) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419863042)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429393469) : eMP 12282 0.011 xi bn ≤ 0.001229856999 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12282 : ℝ) * (1 - 0.011))) ≤ 0.000608020420 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001429393469 / (12282 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000608020420 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000608020420 : ℝ) + 3.141593 * 0.053419863042 / (12282 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001229856999 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419863042)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429393469) : PiBarMP 12282 12 0.011 xi bn ≤ 0.164006090837 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12282 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037807320310 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.212966569274 : ℝ) ≤ √((12282 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.824185086108 : ℝ) ≤ √12282 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12282) ≤ 0.125716315910 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037807320310 + 0.053419863042 * 1.772454 / (2 * (110.212966569274 : ℝ))) * (1 + 0.001229856999) +
        8 / (12282 * 110.824185086108) + 0.125716315910 := by gcongr
    _ ≤ (0.164006090837 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419863042)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429393469) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284507093612) :
    parallelOracle 12282 0.011 xi bn cd ≤ 0.165033256599 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12282 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12282 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484021747 : ℝ) ≤ plow 12282 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.824185086108 : ℝ) ≤ √12282 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284507093612 : ℝ) / (2 * 0.560484021747 * 110.824185086108)) * 0.164006090837 +
        0.284507093612 ^ 2 / (2 * 0.560484021747 * 110.824185086108) := by gcongr
    _ ≤ (0.165033256599 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419863042) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429393469)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284507093612) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12282 12282 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484021747 : ℝ) ≤ plow 12282 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.824185086108 : ℝ) ≤ √12282 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12282 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12282 Θ 1.22 ≤ 0.011965804206 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.824185086108 := by gcongr <;> linarith
      _ ≤ (0.011965804206 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12282 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12282 12282 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12282 12282 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12282 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12282 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12282 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12282 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165033256599 + 0.011965804206 + (0.008646 : ℝ) *
        (1 + 2 * (0.284507093612 + 0.011965804206) / (0.560484021747 * 110.824185086108))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12282]

end BstLean.Part264b.N12282

/-! The original eight local profiles supply actual 12282 moment certificates. -/
namespace BstLean.Part264b.N12282
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12282 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053419863042 ∧
    0 ≤ bN 12282 BstLean.Part154.csC (groupTheta g) ∧ bN 12282 BstLean.Part154.csC (groupTheta g) ≤ 0.001429393469 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12282 12282 0.011
      (momentAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12282 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12282 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12282 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231127374065 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12282 0.011
      (momentAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12282 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12282
/-! The actual computed-centre upper energy formula at 12282. -/
namespace BstLean.Part264b.N12282
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12282

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12282
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12282 cell12282)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086819350913
  | 2 => 0.087789197237
  | 3 => 0.088761550713
  | 4 => 0.089738801159
  | 5 => 0.090723801116
  | 6 => 0.091719929437
  | 7 => 0.092731159948
  | 8 => 0.093762135082
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12282 12282 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12282 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12282

/-! Actual upper energy certificates on all 43 source endpoints at 12282. -/
namespace BstLean.Part264b.N12282
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12282 cell12282)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12282 (gMinus 12282) (1 - (cell12282 i).lower) ≤ 1 ∧
    energyUpper 12282 (gMinus 12282) (BstLean.Part211.gPlus 12282)
      (finiteEnergy 12282 12282 0.011) (1 - (cell12282 i).lower) ≤
      (cell12282 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12282) (by norm_num)
        (q := 1 - (cell12282 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12282,cell12282]) (by norm_num [scalarRow12282,cell12282])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12282,cell12282])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12282

/-! Source-cell containment and simple scalar guards at 12282. -/
namespace BstLean.Part264b.N12282
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12282 cell12282)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12282 ⟨10,by decide⟩).lower ∧ (cell12282 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12282 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12282 ⟨11,by decide⟩).lower ∧ (cell12282 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12282 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12282 ⟨12,by decide⟩).lower ∧ (cell12282 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12282 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12282 ⟨13,by decide⟩).lower ∧ (cell12282 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12282 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12282 ⟨14,by decide⟩).lower ∧ (cell12282 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12282 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12282 ⟨15,by decide⟩).lower ∧ (cell12282 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12282 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12282 ⟨16,by decide⟩).lower ∧ (cell12282 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12282 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12282 ⟨17,by decide⟩).lower ∧ (cell12282 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12282 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12282 ⟨18,by decide⟩).lower ∧ (cell12282 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12282 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12282 ⟨19,by decide⟩).lower ∧ (cell12282 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12282 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12282 ⟨20,by decide⟩).lower ∧ (cell12282 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12282 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12282 ⟨21,by decide⟩).lower ∧ (cell12282 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12282 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12282 ⟨22,by decide⟩).lower ∧ (cell12282 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12282 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12282 ⟨23,by decide⟩).lower ∧ (cell12282 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12282 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12282 ⟨24,by decide⟩).lower ∧ (cell12282 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12282 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12282 ⟨25,by decide⟩).lower ∧ (cell12282 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12282 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12282 ⟨26,by decide⟩).lower ∧ (cell12282 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12282 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12282 ⟨27,by decide⟩).lower ∧ (cell12282 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12282 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12282 ⟨28,by decide⟩).lower ∧ (cell12282 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12282 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12282 ⟨29,by decide⟩).lower ∧ (cell12282 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12282 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12282 ⟨30,by decide⟩).lower ∧ (cell12282 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12282 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12282 ⟨31,by decide⟩).lower ∧ (cell12282 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12282 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12282 ⟨32,by decide⟩).lower ∧ (cell12282 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12282 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12282 ⟨33,by decide⟩).lower ∧ (cell12282 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12282 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12282 ⟨34,by decide⟩).lower ∧ (cell12282 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12282 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12282 ⟨35,by decide⟩).lower ∧ (cell12282 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12282 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12282 ⟨36,by decide⟩).lower ∧ (cell12282 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12282 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12282 ⟨37,by decide⟩).lower ∧ (cell12282 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12282 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12282 ⟨38,by decide⟩).lower ∧ (cell12282 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12282 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12282 ⟨39,by decide⟩).lower ∧ (cell12282 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12282 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12282 ⟨40,by decide⟩).lower ∧ (cell12282 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12282 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12282 ⟨41,by decide⟩).lower ∧ (cell12282 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12282 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12282 ⟨42,by decide⟩).lower ∧ (cell12282 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12282 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12282 ⟨43,by decide⟩).lower ∧ (cell12282 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12282 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12282 ⟨44,by decide⟩).lower ∧ (cell12282 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12282 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12282 ⟨45,by decide⟩).lower ∧ (cell12282 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12282 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12282 ⟨46,by decide⟩).lower ∧ (cell12282 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12282 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12282 ⟨47,by decide⟩).lower ∧ (cell12282 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12282 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12282 ⟨48,by decide⟩).lower ∧ (cell12282 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12282 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12282 ⟨49,by decide⟩).lower ∧ (cell12282 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12282 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12282 ⟨50,by decide⟩).lower ∧ (cell12282 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12282 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12282 ⟨51,by decide⟩).lower ∧ (cell12282 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12282 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12282 ⟨52,by decide⟩).lower ∧ (cell12282 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12282 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12282 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12282 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12282,cell12282,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12282 i).lower ∧
    (cell12282 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12282 i).upper ≤ (0.532 : ℝ) ∧
    (cell12282 i).centre ≤ (0.1 : ℝ) ∧ (cell12282 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12282 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12282 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12282

/-! The local source numeric instances at 12282 have no network premises. -/
namespace BstLean.Part264b.N12282
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12282 cell12282)

noncomputable def sourceNumerics12282 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12282 (cell12282 i)
      scalarRow12282.M scalarRow12282.H scalarRow12282.xi := by
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
    energy_allowance := scalarRow12282.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12282]
    centre_nonneg := (scalarRow12282.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12282]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12282
/-! Actual 12283 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12283
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12283 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12283 12283 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12283.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12283 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12283 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12283 := gPlus_lower 12283
end BstLean.Part264b.N12283

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12283
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036417388795 : ℝ) ≤ wn 12283 := by
  have hn : √(12283 : ℝ) ≤ 110.828696644868 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12283 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.828696644868 ≤ 2 / √12283 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260584974 : ℝ) ≤ rhoBar 12283 BstLean.Part154.csC ∧
    rhoBar 12283 BstLean.Part154.csC ≤ 0.000260607406 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036417388795 : ℝ) / (1.295212 * 12283) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12283) := by gcongr
      _ ≤ (0.000260607406 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12283 BstLean.Part154.csC) ≤ 0.001042497541 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12283 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12283 BstLean.Part154.csC) (piBar (rhoBar 12283 BstLean.Part154.csC)) ≤ 0.000199054016 ∧
    cc1 (rhoBar 12283 BstLean.Part154.csC) (piBar (rhoBar 12283 BstLean.Part154.csC)) ≤ 0.000126659326 ∧
    cc2 (rhoBar 12283 BstLean.Part154.csC) ≤ 0.000073526629 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12283 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12283 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12283 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12283 BstLean.Part154.csC * nuR (rhoBar 12283 BstLean.Part154.csC)) ≤ 0.000521231791 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260607406 : ℝ) * 0.001042497541 := by gcongr
      _ ≤ (0.000521231791 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12283 BstLean.Part154.csC) * nuR (rhoBar 12283 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042497541 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12283 BstLean.Part154.csC) * rhoBar 12283 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260607406 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260607406 / 2 + 0.399 * 0.001042497541 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199054016 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521231791 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126659326 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260607406 / 1.414213562 := by gcongr
      _ ≤ (0.000073526629 : ℝ) := by norm_num

end BstLean.Part264b.N12283

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12283
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12283 BstLean.Part154.csC) (piBar (rhoBar 12283 BstLean.Part154.csC)) ≤ 1.71111E-7 := by
  have hr0 : 0 ≤ rhoBar 12283 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12283 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12283 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12283 BstLean.Part154.csC) (piBar (rhoBar 12283 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12283 BstLean.Part154.csC) (piBar (rhoBar 12283 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12283 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199054016 : ℝ) ^ 2 + 0.000126659326 ^ 2 + 3 * 0.000073526629 ^ 2 +
        2 * 0.797885 * 0.000199054016 * 0.000126659326 + 2 * 0.000199054016 * 0.000073526629 +
        4 * 0.797885 * 0.000126659326 * 0.000073526629 := by gcongr
    _ ≤ (1.71111E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12283 BstLean.Part154.csC Θ ≤ 0.002722450253 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12283 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12283 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12283 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12283 BstLean.Part154.csC) (piBar (rhoBar 12283 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12283 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71111E-7 / (0.000260584974 : ℝ) := by gcongr
    _ ≤ 0.002722450253 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12283 BstLean.Part154.csC Θ ≤ 0.003022468991 + 0.000687857315 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12283 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12283 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12283 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260607406 +
        (6863 / 10000) * 0.000260607406 * 12283 * 0.001042497541) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003022468991 + 0.000687857315 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12283 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12283 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12283 0.011 Θ ∧ gammaRatio 12283 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12283 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12283) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12283 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12283 0.011 Θ) :=
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
    badAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12283 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12283 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12283 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12283 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12283 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12283 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12283 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12283 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12283 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12283 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12283 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004122468991 + 0.003410307568 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12283

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12283
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12283 BstLean.Part154.csC) (piBar (rhoBar 12283 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12283 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12283 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12283 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12283 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12283 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12283 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12283 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12283 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12283 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12283 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12283 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12283 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053377522641 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12283) ≤ 0.010775526712 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12283 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010775526712 + 2 * 0.737676 / 12283) := by gcongr
    _ ≤ (0.053377522641 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12283 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12283

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12283
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484070096 : ℝ) ≤ plow 12283 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12283) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419480465)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429286383) : eMP 12283 0.011 xi bn ≤ 0.001229760723 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12283 : ℝ) * (1 - 0.011))) ≤ 0.000607972894 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001429286383 / (12283 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607972894 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607972894 : ℝ) + 3.141593 * 0.053419480465 / (12283 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001229760723 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419480465)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429286383) : PiBarMP 12283 12 0.011 xi bn ≤ 0.163999530279 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12283 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037805904076 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.217453245844 : ℝ) ≤ √((12283 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.828696644867 : ℝ) ≤ √12283 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12283) ≤ 0.125711198314 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037805904076 + 0.053419480465 * 1.772454 / (2 * (110.217453245844 : ℝ))) * (1 + 0.001229760723) +
        8 / (12283 * 110.828696644867) + 0.125711198314 := by gcongr
    _ ≤ (0.163999530279 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419480465)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429286383) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284504069072) :
    parallelOracle 12283 0.011 xi bn cd ≤ 0.165026621270 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12283 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12283 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484070096 : ℝ) ≤ plow 12283 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.828696644867 : ℝ) ≤ √12283 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284504069072 : ℝ) / (2 * 0.560484070096 * 110.828696644867)) * 0.163999530279 +
        0.284504069072 ^ 2 / (2 * 0.560484070096 * 110.828696644867) := by gcongr
    _ ≤ (0.165026621270 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419480465) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429286383)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284504069072) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12283 12283 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484070096 : ℝ) ≤ plow 12283 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.828696644867 : ℝ) ≤ √12283 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12283 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12283 Θ 1.22 ≤ 0.011965317108 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.828696644867 := by gcongr <;> linarith
      _ ≤ (0.011965317108 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12283 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12283 12283 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12283 12283 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12283 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12283 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12283 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12283 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165026621270 + 0.011965317108 + (0.008646 : ℝ) *
        (1 + 2 * (0.284504069072 + 0.011965317108) / (0.560484070096 * 110.828696644867))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12283]

end BstLean.Part264b.N12283

/-! The original eight local profiles supply actual 12283 moment certificates. -/
namespace BstLean.Part264b.N12283
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12283 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053419480465 ∧
    0 ≤ bN 12283 BstLean.Part154.csC (groupTheta g) ∧ bN 12283 BstLean.Part154.csC (groupTheta g) ≤ 0.001429286383 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12283 12283 0.011
      (momentAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12283 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12283 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12283 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231126546431 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12283 0.011
      (momentAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12283 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12283
/-! The actual computed-centre upper energy formula at 12283. -/
namespace BstLean.Part264b.N12283
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12283

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12283
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12283 cell12283)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086815866510
  | 2 => 0.087785634551
  | 3 => 0.088757896162
  | 4 => 0.089735038224
  | 5 => 0.090719909857
  | 6 => 0.091715885952
  | 7 => 0.092726935781
  | 8 => 0.093757696568
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12283 12283 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12283 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12283

/-! Actual upper energy certificates on all 43 source endpoints at 12283. -/
namespace BstLean.Part264b.N12283
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12283 cell12283)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12283 (gMinus 12283) (1 - (cell12283 i).lower) ≤ 1 ∧
    energyUpper 12283 (gMinus 12283) (BstLean.Part211.gPlus 12283)
      (finiteEnergy 12283 12283 0.011) (1 - (cell12283 i).lower) ≤
      (cell12283 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12283) (by norm_num)
        (q := 1 - (cell12283 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12283,cell12283]) (by norm_num [scalarRow12283,cell12283])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12283,cell12283])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12283

/-! Source-cell containment and simple scalar guards at 12283. -/
namespace BstLean.Part264b.N12283
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12283 cell12283)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12283 ⟨10,by decide⟩).lower ∧ (cell12283 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12283 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12283 ⟨11,by decide⟩).lower ∧ (cell12283 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12283 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12283 ⟨12,by decide⟩).lower ∧ (cell12283 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12283 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12283 ⟨13,by decide⟩).lower ∧ (cell12283 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12283 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12283 ⟨14,by decide⟩).lower ∧ (cell12283 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12283 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12283 ⟨15,by decide⟩).lower ∧ (cell12283 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12283 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12283 ⟨16,by decide⟩).lower ∧ (cell12283 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12283 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12283 ⟨17,by decide⟩).lower ∧ (cell12283 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12283 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12283 ⟨18,by decide⟩).lower ∧ (cell12283 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12283 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12283 ⟨19,by decide⟩).lower ∧ (cell12283 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12283 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12283 ⟨20,by decide⟩).lower ∧ (cell12283 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12283 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12283 ⟨21,by decide⟩).lower ∧ (cell12283 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12283 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12283 ⟨22,by decide⟩).lower ∧ (cell12283 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12283 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12283 ⟨23,by decide⟩).lower ∧ (cell12283 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12283 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12283 ⟨24,by decide⟩).lower ∧ (cell12283 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12283 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12283 ⟨25,by decide⟩).lower ∧ (cell12283 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12283 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12283 ⟨26,by decide⟩).lower ∧ (cell12283 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12283 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12283 ⟨27,by decide⟩).lower ∧ (cell12283 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12283 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12283 ⟨28,by decide⟩).lower ∧ (cell12283 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12283 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12283 ⟨29,by decide⟩).lower ∧ (cell12283 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12283 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12283 ⟨30,by decide⟩).lower ∧ (cell12283 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12283 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12283 ⟨31,by decide⟩).lower ∧ (cell12283 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12283 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12283 ⟨32,by decide⟩).lower ∧ (cell12283 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12283 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12283 ⟨33,by decide⟩).lower ∧ (cell12283 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12283 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12283 ⟨34,by decide⟩).lower ∧ (cell12283 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12283 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12283 ⟨35,by decide⟩).lower ∧ (cell12283 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12283 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12283 ⟨36,by decide⟩).lower ∧ (cell12283 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12283 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12283 ⟨37,by decide⟩).lower ∧ (cell12283 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12283 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12283 ⟨38,by decide⟩).lower ∧ (cell12283 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12283 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12283 ⟨39,by decide⟩).lower ∧ (cell12283 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12283 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12283 ⟨40,by decide⟩).lower ∧ (cell12283 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12283 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12283 ⟨41,by decide⟩).lower ∧ (cell12283 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12283 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12283 ⟨42,by decide⟩).lower ∧ (cell12283 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12283 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12283 ⟨43,by decide⟩).lower ∧ (cell12283 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12283 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12283 ⟨44,by decide⟩).lower ∧ (cell12283 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12283 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12283 ⟨45,by decide⟩).lower ∧ (cell12283 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12283 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12283 ⟨46,by decide⟩).lower ∧ (cell12283 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12283 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12283 ⟨47,by decide⟩).lower ∧ (cell12283 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12283 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12283 ⟨48,by decide⟩).lower ∧ (cell12283 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12283 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12283 ⟨49,by decide⟩).lower ∧ (cell12283 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12283 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12283 ⟨50,by decide⟩).lower ∧ (cell12283 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12283 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12283 ⟨51,by decide⟩).lower ∧ (cell12283 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12283 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12283 ⟨52,by decide⟩).lower ∧ (cell12283 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12283 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12283 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12283 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12283,cell12283,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12283 i).lower ∧
    (cell12283 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12283 i).upper ≤ (0.532 : ℝ) ∧
    (cell12283 i).centre ≤ (0.1 : ℝ) ∧ (cell12283 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12283 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12283 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12283

/-! The local source numeric instances at 12283 have no network premises. -/
namespace BstLean.Part264b.N12283
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12283 cell12283)

noncomputable def sourceNumerics12283 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12283 (cell12283 i)
      scalarRow12283.M scalarRow12283.H scalarRow12283.xi := by
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
    energy_allowance := scalarRow12283.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12283]
    centre_nonneg := (scalarRow12283.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12283]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12283
/-! Actual 12284 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12284
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12284 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12284 12284 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12284.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12284 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12284 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12284 := gPlus_lower 12284
end BstLean.Part264b.N12284

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12284
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036415893200 : ℝ) ≤ wn 12284 := by
  have hn : √(12284 : ℝ) ≤ 110.833208019980 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12284 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.833208019980 ≤ 2 / √12284 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260563385 : ℝ) ≤ rhoBar 12284 BstLean.Part154.csC ∧
    rhoBar 12284 BstLean.Part154.csC ≤ 0.000260586190 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036415893200 : ℝ) / (1.295212 * 12284) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12284) := by gcongr
      _ ≤ (0.000260586190 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12284 BstLean.Part154.csC) ≤ 0.001042412666 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12284 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12284 BstLean.Part154.csC) (piBar (rhoBar 12284 BstLean.Part154.csC)) ≤ 0.000199037810 ∧
    cc1 (rhoBar 12284 BstLean.Part154.csC) (piBar (rhoBar 12284 BstLean.Part154.csC)) ≤ 0.000126649014 ∧
    cc2 (rhoBar 12284 BstLean.Part154.csC) ≤ 0.000073520643 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12284 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12284 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12284 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12284 BstLean.Part154.csC * nuR (rhoBar 12284 BstLean.Part154.csC)) ≤ 0.000521189357 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260586190 : ℝ) * 0.001042412666 := by gcongr
      _ ≤ (0.000521189357 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12284 BstLean.Part154.csC) * nuR (rhoBar 12284 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042412666 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12284 BstLean.Part154.csC) * rhoBar 12284 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260586190 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260586190 / 2 + 0.399 * 0.001042412666 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199037810 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521189357 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126649014 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260586190 / 1.414213562 := by gcongr
      _ ≤ (0.000073520643 : ℝ) := by norm_num

end BstLean.Part264b.N12284

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12284
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12284 BstLean.Part154.csC) (piBar (rhoBar 12284 BstLean.Part154.csC)) ≤ 1.71083E-7 := by
  have hr0 : 0 ≤ rhoBar 12284 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12284 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12284 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12284 BstLean.Part154.csC) (piBar (rhoBar 12284 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12284 BstLean.Part154.csC) (piBar (rhoBar 12284 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12284 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199037810 : ℝ) ^ 2 + 0.000126649014 ^ 2 + 3 * 0.000073520643 ^ 2 +
        2 * 0.797885 * 0.000199037810 * 0.000126649014 + 2 * 0.000199037810 * 0.000073520643 +
        4 * 0.797885 * 0.000126649014 * 0.000073520643 := by gcongr
    _ ≤ (1.71083E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12284 BstLean.Part154.csC Θ ≤ 0.002722230293 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12284 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12284 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12284 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12284 BstLean.Part154.csC) (piBar (rhoBar 12284 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12284 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71083E-7 / (0.000260563385 : ℝ) := by gcongr
    _ ≤ 0.002722230293 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12284 BstLean.Part154.csC Θ ≤ 0.003022222907 + 0.000687801316 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12284 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12284 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12284 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260586190 +
        (6863 / 10000) * 0.000260586190 * 12284 * 0.001042412666) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003022222907 + 0.000687801316 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12284 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12284 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12284 0.011 Θ ∧ gammaRatio 12284 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12284 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12284) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12284 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12284 0.011 Θ) :=
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
    badAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12284 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12284 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12284 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12284 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12284 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12284 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12284 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12284 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12284 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12284 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12284 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004122222907 + 0.003410031609 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12284

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12284
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12284 BstLean.Part154.csC) (piBar (rhoBar 12284 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12284 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12284 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12284 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12284 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12284 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12284 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12284 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12284 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12284 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12284 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12284 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12284 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053375326001 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12284) ≤ 0.010775088103 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12284 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010775088103 + 2 * 0.737676 / 12284) := by gcongr
    _ ≤ (0.053375326001 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12284 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12284

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12284
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484118438 : ℝ) ≤ plow 12284 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12284) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419089502)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429170904) : eMP 12284 0.011 xi bn ≤ 0.001229660883 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12284 : ℝ) * (1 - 0.011))) ≤ 0.000607923587 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001429170904 / (12284 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607923587 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607923587 : ℝ) + 3.141593 * 0.053419089502 / (12284 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001229660883 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419089502)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429170904) : PiBarMP 12284 12 0.011 xi bn ≤ 0.163992858949 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12284 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037804376784 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.221939739781 : ℝ) ≤ √((12284 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.833208019979 : ℝ) ≤ √12284 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12284) ≤ 0.125706081342 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037804376784 + 0.053419089502 * 1.772454 / (2 * (110.221939739781 : ℝ))) * (1 + 0.001229660883) +
        8 / (12284 * 110.833208019979) + 0.125706081342 := by gcongr
    _ ≤ (0.163992858949 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419089502)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429170904) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284501026654) :
    parallelOracle 12284 0.011 xi bn cd ≤ 0.165019874818 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12284 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12284 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484118438 : ℝ) ≤ plow 12284 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.833208019979 : ℝ) ≤ √12284 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284501026654 : ℝ) / (2 * 0.560484118438 * 110.833208019979)) * 0.163992858949 +
        0.284501026654 ^ 2 / (2 * 0.560484118438 * 110.833208019979) := by gcongr
    _ ≤ (0.165019874818 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053419089502) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429170904)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284501026654) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12284 12284 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484118438 : ℝ) ≤ plow 12284 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.833208019979 : ℝ) ≤ √12284 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12284 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12284 Θ 1.22 ≤ 0.011964830070 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.833208019979 := by gcongr <;> linarith
      _ ≤ (0.011964830070 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12284 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12284 12284 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12284 12284 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12284 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12284 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12284 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12284 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165019874818 + 0.011964830070 + (0.008646 : ℝ) *
        (1 + 2 * (0.284501026654 + 0.011964830070) / (0.560484118438 * 110.833208019979))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12284]

end BstLean.Part264b.N12284

/-! The original eight local profiles supply actual 12284 moment certificates. -/
namespace BstLean.Part264b.N12284
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12284 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053419089502 ∧
    0 ≤ bN 12284 BstLean.Part154.csC (groupTheta g) ∧ bN 12284 BstLean.Part154.csC (groupTheta g) ≤ 0.001429170904 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12284 12284 0.011
      (momentAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12284 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12284 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12284 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231125700653 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12284 0.011
      (momentAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12284 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12284
/-! The actual computed-centre upper energy formula at 12284. -/
namespace BstLean.Part264b.N12284
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12284

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12284
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12284 cell12284)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086812383798
  | 2 => 0.087782073633
  | 3 => 0.088754243474
  | 4 => 0.089731277268
  | 5 => 0.090716020717
  | 6 => 0.091711844757
  | 7 => 0.092722714109
  | 8 => 0.093753260794
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12284 12284 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12284 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12284

/-! Actual upper energy certificates on all 43 source endpoints at 12284. -/
namespace BstLean.Part264b.N12284
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12284 cell12284)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12284 (gMinus 12284) (1 - (cell12284 i).lower) ≤ 1 ∧
    energyUpper 12284 (gMinus 12284) (BstLean.Part211.gPlus 12284)
      (finiteEnergy 12284 12284 0.011) (1 - (cell12284 i).lower) ≤
      (cell12284 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12284) (by norm_num)
        (q := 1 - (cell12284 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12284,cell12284]) (by norm_num [scalarRow12284,cell12284])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12284,cell12284])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12284

/-! Source-cell containment and simple scalar guards at 12284. -/
namespace BstLean.Part264b.N12284
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12284 cell12284)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12284 ⟨10,by decide⟩).lower ∧ (cell12284 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12284 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12284 ⟨11,by decide⟩).lower ∧ (cell12284 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12284 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12284 ⟨12,by decide⟩).lower ∧ (cell12284 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12284 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12284 ⟨13,by decide⟩).lower ∧ (cell12284 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12284 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12284 ⟨14,by decide⟩).lower ∧ (cell12284 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12284 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12284 ⟨15,by decide⟩).lower ∧ (cell12284 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12284 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12284 ⟨16,by decide⟩).lower ∧ (cell12284 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12284 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12284 ⟨17,by decide⟩).lower ∧ (cell12284 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12284 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12284 ⟨18,by decide⟩).lower ∧ (cell12284 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12284 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12284 ⟨19,by decide⟩).lower ∧ (cell12284 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12284 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12284 ⟨20,by decide⟩).lower ∧ (cell12284 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12284 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12284 ⟨21,by decide⟩).lower ∧ (cell12284 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12284 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12284 ⟨22,by decide⟩).lower ∧ (cell12284 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12284 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12284 ⟨23,by decide⟩).lower ∧ (cell12284 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12284 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12284 ⟨24,by decide⟩).lower ∧ (cell12284 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12284 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12284 ⟨25,by decide⟩).lower ∧ (cell12284 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12284 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12284 ⟨26,by decide⟩).lower ∧ (cell12284 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12284 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12284 ⟨27,by decide⟩).lower ∧ (cell12284 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12284 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12284 ⟨28,by decide⟩).lower ∧ (cell12284 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12284 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12284 ⟨29,by decide⟩).lower ∧ (cell12284 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12284 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12284 ⟨30,by decide⟩).lower ∧ (cell12284 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12284 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12284 ⟨31,by decide⟩).lower ∧ (cell12284 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12284 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12284 ⟨32,by decide⟩).lower ∧ (cell12284 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12284 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12284 ⟨33,by decide⟩).lower ∧ (cell12284 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12284 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12284 ⟨34,by decide⟩).lower ∧ (cell12284 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12284 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12284 ⟨35,by decide⟩).lower ∧ (cell12284 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12284 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12284 ⟨36,by decide⟩).lower ∧ (cell12284 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12284 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12284 ⟨37,by decide⟩).lower ∧ (cell12284 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12284 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12284 ⟨38,by decide⟩).lower ∧ (cell12284 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12284 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12284 ⟨39,by decide⟩).lower ∧ (cell12284 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12284 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12284 ⟨40,by decide⟩).lower ∧ (cell12284 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12284 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12284 ⟨41,by decide⟩).lower ∧ (cell12284 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12284 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12284 ⟨42,by decide⟩).lower ∧ (cell12284 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12284 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12284 ⟨43,by decide⟩).lower ∧ (cell12284 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12284 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12284 ⟨44,by decide⟩).lower ∧ (cell12284 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12284 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12284 ⟨45,by decide⟩).lower ∧ (cell12284 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12284 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12284 ⟨46,by decide⟩).lower ∧ (cell12284 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12284 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12284 ⟨47,by decide⟩).lower ∧ (cell12284 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12284 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12284 ⟨48,by decide⟩).lower ∧ (cell12284 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12284 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12284 ⟨49,by decide⟩).lower ∧ (cell12284 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12284 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12284 ⟨50,by decide⟩).lower ∧ (cell12284 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12284 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12284 ⟨51,by decide⟩).lower ∧ (cell12284 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12284 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12284 ⟨52,by decide⟩).lower ∧ (cell12284 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12284 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12284 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12284 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12284,cell12284,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12284 i).lower ∧
    (cell12284 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12284 i).upper ≤ (0.532 : ℝ) ∧
    (cell12284 i).centre ≤ (0.1 : ℝ) ∧ (cell12284 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12284 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12284 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12284

/-! The local source numeric instances at 12284 have no network premises. -/
namespace BstLean.Part264b.N12284
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12284 cell12284)

noncomputable def sourceNumerics12284 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12284 (cell12284 i)
      scalarRow12284.M scalarRow12284.H scalarRow12284.xi := by
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
    energy_allowance := scalarRow12284.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12284]
    centre_nonneg := (scalarRow12284.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12284]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12284
/-! Actual 12285 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12285
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12285 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12285 12285 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12285.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12285 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12285 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12285 := gPlus_lower 12285
end BstLean.Part264b.N12285

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12285
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036414397789 : ℝ) ≤ wn 12285 := by
  have hn : √(12285 : ℝ) ≤ 110.837719211467 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12285 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.837719211467 ≤ 2 / √12285 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260541799 : ℝ) ≤ rhoBar 12285 BstLean.Part154.csC ∧
    rhoBar 12285 BstLean.Part154.csC ≤ 0.000260564979 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036414397789 : ℝ) / (1.295212 * 12285) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12285) := by gcongr
      _ ≤ (0.000260564979 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12285 BstLean.Part154.csC) ≤ 0.001042327811 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12285 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12285 BstLean.Part154.csC) (piBar (rhoBar 12285 BstLean.Part154.csC)) ≤ 0.000199021608 ∧
    cc1 (rhoBar 12285 BstLean.Part154.csC) (piBar (rhoBar 12285 BstLean.Part154.csC)) ≤ 0.000126638705 ∧
    cc2 (rhoBar 12285 BstLean.Part154.csC) ≤ 0.000073514659 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12285 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12285 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12285 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12285 BstLean.Part154.csC * nuR (rhoBar 12285 BstLean.Part154.csC)) ≤ 0.000521146932 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260564979 : ℝ) * 0.001042327811 := by gcongr
      _ ≤ (0.000521146932 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12285 BstLean.Part154.csC) * nuR (rhoBar 12285 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042327811 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12285 BstLean.Part154.csC) * rhoBar 12285 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260564979 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260564979 / 2 + 0.399 * 0.001042327811 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199021608 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521146932 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126638705 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260564979 / 1.414213562 := by gcongr
      _ ≤ (0.000073514659 : ℝ) := by norm_num

end BstLean.Part264b.N12285

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12285
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12285 BstLean.Part154.csC) (piBar (rhoBar 12285 BstLean.Part154.csC)) ≤ 1.71055E-7 := by
  have hr0 : 0 ≤ rhoBar 12285 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12285 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12285 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12285 BstLean.Part154.csC) (piBar (rhoBar 12285 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12285 BstLean.Part154.csC) (piBar (rhoBar 12285 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12285 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199021608 : ℝ) ^ 2 + 0.000126638705 ^ 2 + 3 * 0.000073514659 ^ 2 +
        2 * 0.797885 * 0.000199021608 * 0.000126638705 + 2 * 0.000199021608 * 0.000073514659 +
        4 * 0.797885 * 0.000126638705 * 0.000073514659 := by gcongr
    _ ≤ (1.71055E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12285 BstLean.Part154.csC Θ ≤ 0.002722010265 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12285 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12285 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12285 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12285 BstLean.Part154.csC) (piBar (rhoBar 12285 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12285 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71055E-7 / (0.000260541799 : ℝ) := by gcongr
    _ ≤ 0.002722010265 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12285 BstLean.Part154.csC Θ ≤ 0.003021976899 + 0.000687745331 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12285 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12285 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12285 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260564979 +
        (6863 / 10000) * 0.000260564979 * 12285 * 0.001042327811) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003021976899 + 0.000687745331 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12285 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12285 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12285 0.011 Θ ∧ gammaRatio 12285 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12285 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12285) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12285 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12285 0.011 Θ) :=
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
    badAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12285 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12285 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12285 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12285 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12285 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12285 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12285 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12285 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12285 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12285 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12285 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004121976899 + 0.003409755596 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12285

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12285
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12285 BstLean.Part154.csC) (piBar (rhoBar 12285 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12285 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12285 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12285 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12285 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12285 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12285 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12285 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12285 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12285 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12285 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12285 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12285 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053373129630 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12285) ≤ 0.010774649547 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12285 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010774649547 + 2 * 0.737676 / 12285) := by gcongr
    _ ≤ (0.053373129630 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12285 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12285

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12285
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484166772 : ℝ) ≤ plow 12285 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12285) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053418698587)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429055390) : eMP 12285 0.011 xi bn ≤ 0.001229561036 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12285 : ℝ) * (1 - 0.011))) ≤ 0.000607874276 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001429055390 / (12285 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607874276 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607874276 : ℝ) + 3.141593 * 0.053418698587 / (12285 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001229561036 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053418698587)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429055390) : PiBarMP 12285 12 0.011 xi bn ≤ 0.163986187723 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12285 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037802848967 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.226426051106 : ℝ) ≤ √((12285 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.837719211466 : ℝ) ≤ √12285 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12285) ≤ 0.125700964996 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037802848967 + 0.053418698587 * 1.772454 / (2 * (110.226426051106 : ℝ))) * (1 + 0.001229561036) +
        8 / (12285 * 110.837719211466) + 0.125700964996 := by gcongr
    _ ≤ (0.163986187723 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053418698587)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429055390) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284497984605) :
    parallelOracle 12285 0.011 xi bn cd ≤ 0.165013128480 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12285 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12285 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484166772 : ℝ) ≤ plow 12285 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.837719211466 : ℝ) ≤ √12285 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284497984605 : ℝ) / (2 * 0.560484166772 * 110.837719211466)) * 0.163986187723 +
        0.284497984605 ^ 2 / (2 * 0.560484166772 * 110.837719211466) := by gcongr
    _ ≤ (0.165013128480 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053418698587) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001429055390)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284497984605) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12285 12285 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484166772 : ℝ) ≤ plow 12285 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.837719211466 : ℝ) ≤ √12285 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12285 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12285 Θ 1.22 ≤ 0.011964343091 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.837719211466 := by gcongr <;> linarith
      _ ≤ (0.011964343091 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12285 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12285 12285 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12285 12285 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12285 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12285 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12285 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12285 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165013128480 + 0.011964343091 + (0.008646 : ℝ) *
        (1 + 2 * (0.284497984605 + 0.011964343091) / (0.560484166772 * 110.837719211466))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12285]

end BstLean.Part264b.N12285

/-! The original eight local profiles supply actual 12285 moment certificates. -/
namespace BstLean.Part264b.N12285
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12285 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053418698587 ∧
    0 ≤ bN 12285 BstLean.Part154.csC (groupTheta g) ∧ bN 12285 BstLean.Part154.csC (groupTheta g) ≤ 0.001429055390 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12285 12285 0.011
      (momentAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12285 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12285 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12285 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231124854975 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12285 0.011
      (momentAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12285 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12285
/-! The actual computed-centre upper energy formula at 12285. -/
namespace BstLean.Part264b.N12285
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12285

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12285
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12285 cell12285)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086808902776
  | 2 => 0.087778514482
  | 3 => 0.088750592647
  | 4 => 0.089727518288
  | 5 => 0.090712133695
  | 6 => 0.091707805850
  | 7 => 0.092718494929
  | 8 => 0.093748827757
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12285 12285 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12285 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12285

/-! Actual upper energy certificates on all 43 source endpoints at 12285. -/
namespace BstLean.Part264b.N12285
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12285 cell12285)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12285 (gMinus 12285) (1 - (cell12285 i).lower) ≤ 1 ∧
    energyUpper 12285 (gMinus 12285) (BstLean.Part211.gPlus 12285)
      (finiteEnergy 12285 12285 0.011) (1 - (cell12285 i).lower) ≤
      (cell12285 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12285) (by norm_num)
        (q := 1 - (cell12285 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12285,cell12285]) (by norm_num [scalarRow12285,cell12285])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12285,cell12285])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12285

/-! Source-cell containment and simple scalar guards at 12285. -/
namespace BstLean.Part264b.N12285
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12285 cell12285)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12285 ⟨10,by decide⟩).lower ∧ (cell12285 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12285 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12285 ⟨11,by decide⟩).lower ∧ (cell12285 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12285 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12285 ⟨12,by decide⟩).lower ∧ (cell12285 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12285 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12285 ⟨13,by decide⟩).lower ∧ (cell12285 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12285 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12285 ⟨14,by decide⟩).lower ∧ (cell12285 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12285 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12285 ⟨15,by decide⟩).lower ∧ (cell12285 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12285 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12285 ⟨16,by decide⟩).lower ∧ (cell12285 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12285 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12285 ⟨17,by decide⟩).lower ∧ (cell12285 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12285 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12285 ⟨18,by decide⟩).lower ∧ (cell12285 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12285 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12285 ⟨19,by decide⟩).lower ∧ (cell12285 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12285 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12285 ⟨20,by decide⟩).lower ∧ (cell12285 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12285 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12285 ⟨21,by decide⟩).lower ∧ (cell12285 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12285 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12285 ⟨22,by decide⟩).lower ∧ (cell12285 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12285 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12285 ⟨23,by decide⟩).lower ∧ (cell12285 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12285 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12285 ⟨24,by decide⟩).lower ∧ (cell12285 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12285 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12285 ⟨25,by decide⟩).lower ∧ (cell12285 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12285 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12285 ⟨26,by decide⟩).lower ∧ (cell12285 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12285 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12285 ⟨27,by decide⟩).lower ∧ (cell12285 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12285 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12285 ⟨28,by decide⟩).lower ∧ (cell12285 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12285 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12285 ⟨29,by decide⟩).lower ∧ (cell12285 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12285 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12285 ⟨30,by decide⟩).lower ∧ (cell12285 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12285 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12285 ⟨31,by decide⟩).lower ∧ (cell12285 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12285 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12285 ⟨32,by decide⟩).lower ∧ (cell12285 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12285 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12285 ⟨33,by decide⟩).lower ∧ (cell12285 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12285 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12285 ⟨34,by decide⟩).lower ∧ (cell12285 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12285 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12285 ⟨35,by decide⟩).lower ∧ (cell12285 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12285 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12285 ⟨36,by decide⟩).lower ∧ (cell12285 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12285 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12285 ⟨37,by decide⟩).lower ∧ (cell12285 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12285 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12285 ⟨38,by decide⟩).lower ∧ (cell12285 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12285 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12285 ⟨39,by decide⟩).lower ∧ (cell12285 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12285 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12285 ⟨40,by decide⟩).lower ∧ (cell12285 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12285 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12285 ⟨41,by decide⟩).lower ∧ (cell12285 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12285 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12285 ⟨42,by decide⟩).lower ∧ (cell12285 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12285 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12285 ⟨43,by decide⟩).lower ∧ (cell12285 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12285 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12285 ⟨44,by decide⟩).lower ∧ (cell12285 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12285 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12285 ⟨45,by decide⟩).lower ∧ (cell12285 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12285 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12285 ⟨46,by decide⟩).lower ∧ (cell12285 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12285 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12285 ⟨47,by decide⟩).lower ∧ (cell12285 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12285 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12285 ⟨48,by decide⟩).lower ∧ (cell12285 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12285 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12285 ⟨49,by decide⟩).lower ∧ (cell12285 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12285 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12285 ⟨50,by decide⟩).lower ∧ (cell12285 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12285 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12285 ⟨51,by decide⟩).lower ∧ (cell12285 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12285 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12285 ⟨52,by decide⟩).lower ∧ (cell12285 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12285 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12285 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12285 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12285,cell12285,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12285 i).lower ∧
    (cell12285 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12285 i).upper ≤ (0.532 : ℝ) ∧
    (cell12285 i).centre ≤ (0.1 : ℝ) ∧ (cell12285 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12285 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12285 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12285

/-! The local source numeric instances at 12285 have no network premises. -/
namespace BstLean.Part264b.N12285
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12285 cell12285)

noncomputable def sourceNumerics12285 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12285 (cell12285 i)
      scalarRow12285.M scalarRow12285.H scalarRow12285.xi := by
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
    energy_allowance := scalarRow12285.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12285]
    centre_nonneg := (scalarRow12285.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12285]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12285
/-! Actual 12286 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12286
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12286 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12286 12286 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12286.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12286 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12286 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12286 := gPlus_lower 12286
end BstLean.Part264b.N12286

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12286
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036412902562 : ℝ) ≤ wn 12286 := by
  have hn : √(12286 : ℝ) ≤ 110.842230219353 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12286 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.842230219353 ≤ 2 / √12286 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260520217 : ℝ) ≤ rhoBar 12286 BstLean.Part154.csC ∧
    rhoBar 12286 BstLean.Part154.csC ≤ 0.000260543770 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036412902562 : ℝ) / (1.295212 * 12286) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12286) := by gcongr
      _ ≤ (0.000260543770 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12286 BstLean.Part154.csC) ≤ 0.001042242964 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12286 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12286 BstLean.Part154.csC) (piBar (rhoBar 12286 BstLean.Part154.csC)) ≤ 0.000199005408 ∧
    cc1 (rhoBar 12286 BstLean.Part154.csC) (piBar (rhoBar 12286 BstLean.Part154.csC)) ≤ 0.000126628397 ∧
    cc2 (rhoBar 12286 BstLean.Part154.csC) ≤ 0.000073508675 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12286 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12286 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12286 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12286 BstLean.Part154.csC * nuR (rhoBar 12286 BstLean.Part154.csC)) ≤ 0.000521104511 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260543770 : ℝ) * 0.001042242964 := by gcongr
      _ ≤ (0.000521104511 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12286 BstLean.Part154.csC) * nuR (rhoBar 12286 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042242964 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12286 BstLean.Part154.csC) * rhoBar 12286 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260543770 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260543770 / 2 + 0.399 * 0.001042242964 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199005408 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521104511 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126628397 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260543770 / 1.414213562 := by gcongr
      _ ≤ (0.000073508675 : ℝ) := by norm_num

end BstLean.Part264b.N12286

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12286
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12286 BstLean.Part154.csC) (piBar (rhoBar 12286 BstLean.Part154.csC)) ≤ 1.71027E-7 := by
  have hr0 : 0 ≤ rhoBar 12286 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12286 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12286 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12286 BstLean.Part154.csC) (piBar (rhoBar 12286 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12286 BstLean.Part154.csC) (piBar (rhoBar 12286 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12286 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199005408 : ℝ) ^ 2 + 0.000126628397 ^ 2 + 3 * 0.000073508675 ^ 2 +
        2 * 0.797885 * 0.000199005408 * 0.000126628397 + 2 * 0.000199005408 * 0.000073508675 +
        4 * 0.797885 * 0.000126628397 * 0.000073508675 := by gcongr
    _ ≤ (1.71027E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12286 BstLean.Part154.csC Θ ≤ 0.002721790158 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12286 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12286 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12286 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12286 BstLean.Part154.csC) (piBar (rhoBar 12286 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12286 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71027E-7 / (0.000260520217 : ℝ) := by gcongr
    _ ≤ 0.002721790158 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12286 BstLean.Part154.csC Θ ≤ 0.003021730897 + 0.000687689351 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12286 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12286 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12286 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260543770 +
        (6863 / 10000) * 0.000260543770 * 12286 * 0.001042242964) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003021730897 + 0.000687689351 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12286 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12286 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12286 0.011 Θ ∧ gammaRatio 12286 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12286 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12286) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12286 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12286 0.011 Θ) :=
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
    badAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12286 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12286 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12286 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12286 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12286 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12286 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12286 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12286 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12286 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12286 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12286 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004121730897 + 0.003409479509 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12286

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12286
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12286 BstLean.Part154.csC) (piBar (rhoBar 12286 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12286 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12286 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12286 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12286 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12286 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12286 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12286 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12286 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12286 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12286 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12286 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12286 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053370933530 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12286) ≤ 0.010774211045 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12286 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010774211045 + 2 * 0.737676 / 12286) := by gcongr
    _ ≤ (0.053370933530 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12286 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12286

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12286
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484215098 : ℝ) ≤ plow 12286 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12286) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053418307640)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428939833) : eMP 12286 0.011 xi bn ≤ 0.001229461181 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12286 : ℝ) * (1 - 0.011))) ≤ 0.000607824961 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001428939833 / (12286 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607824961 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607824961 : ℝ) + 3.141593 * 0.053418307640 / (12286 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001229461181 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053418307640)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428939833) : PiBarMP 12286 12 0.011 xi bn ≤ 0.163979516492 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12286 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037801320520 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.230912179841 : ℝ) ≤ √((12286 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.842230219352 : ℝ) ≤ √12286 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12286) ≤ 0.125695849274 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037801320520 + 0.053418307640 * 1.772454 / (2 * (110.230912179841 : ℝ))) * (1 + 0.001229461181) +
        8 / (12286 * 110.842230219352) + 0.125695849274 := by gcongr
    _ ≤ (0.163979516492 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053418307640)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428939833) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284494942755) :
    parallelOracle 12286 0.011 xi bn cd ≤ 0.165006382147 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12286 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12286 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484215098 : ℝ) ≤ plow 12286 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.842230219352 : ℝ) ≤ √12286 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284494942755 : ℝ) / (2 * 0.560484215098 * 110.842230219352)) * 0.163979516492 +
        0.284494942755 ^ 2 / (2 * 0.560484215098 * 110.842230219352) := by gcongr
    _ ≤ (0.165006382147 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053418307640) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428939833)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284494942755) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12286 12286 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484215098 : ℝ) ≤ plow 12286 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.842230219352 : ℝ) ≤ √12286 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12286 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12286 Θ 1.22 ≤ 0.011963856171 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.842230219352 := by gcongr <;> linarith
      _ ≤ (0.011963856171 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12286 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12286 12286 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12286 12286 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12286 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12286 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12286 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12286 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165006382147 + 0.011963856171 + (0.008646 : ℝ) *
        (1 + 2 * (0.284494942755 + 0.011963856171) / (0.560484215098 * 110.842230219352))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12286]

end BstLean.Part264b.N12286

/-! The original eight local profiles supply actual 12286 moment certificates. -/
namespace BstLean.Part264b.N12286
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12286 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053418307640 ∧
    0 ≤ bN 12286 BstLean.Part154.csC (groupTheta g) ∧ bN 12286 BstLean.Part154.csC (groupTheta g) ≤ 0.001428939833 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12286 12286 0.011
      (momentAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12286 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12286 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12286 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231124009225 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12286 0.011
      (momentAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12286 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12286
/-! The actual computed-centre upper energy formula at 12286. -/
namespace BstLean.Part264b.N12286
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12286

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12286
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12286 cell12286)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086805423442
  | 2 => 0.087774957095
  | 3 => 0.088746943678
  | 4 => 0.089723761283
  | 5 => 0.090708248787
  | 6 => 0.091703769228
  | 7 => 0.092714278238
  | 8 => 0.093744397453
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12286 12286 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12286 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12286

/-! Actual upper energy certificates on all 43 source endpoints at 12286. -/
namespace BstLean.Part264b.N12286
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12286 cell12286)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12286 (gMinus 12286) (1 - (cell12286 i).lower) ≤ 1 ∧
    energyUpper 12286 (gMinus 12286) (BstLean.Part211.gPlus 12286)
      (finiteEnergy 12286 12286 0.011) (1 - (cell12286 i).lower) ≤
      (cell12286 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12286) (by norm_num)
        (q := 1 - (cell12286 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12286,cell12286]) (by norm_num [scalarRow12286,cell12286])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12286,cell12286])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12286

/-! Source-cell containment and simple scalar guards at 12286. -/
namespace BstLean.Part264b.N12286
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12286 cell12286)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12286 ⟨10,by decide⟩).lower ∧ (cell12286 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12286 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12286 ⟨11,by decide⟩).lower ∧ (cell12286 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12286 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12286 ⟨12,by decide⟩).lower ∧ (cell12286 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12286 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12286 ⟨13,by decide⟩).lower ∧ (cell12286 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12286 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12286 ⟨14,by decide⟩).lower ∧ (cell12286 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12286 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12286 ⟨15,by decide⟩).lower ∧ (cell12286 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12286 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12286 ⟨16,by decide⟩).lower ∧ (cell12286 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12286 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12286 ⟨17,by decide⟩).lower ∧ (cell12286 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12286 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12286 ⟨18,by decide⟩).lower ∧ (cell12286 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12286 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12286 ⟨19,by decide⟩).lower ∧ (cell12286 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12286 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12286 ⟨20,by decide⟩).lower ∧ (cell12286 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12286 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12286 ⟨21,by decide⟩).lower ∧ (cell12286 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12286 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12286 ⟨22,by decide⟩).lower ∧ (cell12286 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12286 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12286 ⟨23,by decide⟩).lower ∧ (cell12286 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12286 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12286 ⟨24,by decide⟩).lower ∧ (cell12286 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12286 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12286 ⟨25,by decide⟩).lower ∧ (cell12286 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12286 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12286 ⟨26,by decide⟩).lower ∧ (cell12286 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12286 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12286 ⟨27,by decide⟩).lower ∧ (cell12286 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12286 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12286 ⟨28,by decide⟩).lower ∧ (cell12286 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12286 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12286 ⟨29,by decide⟩).lower ∧ (cell12286 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12286 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12286 ⟨30,by decide⟩).lower ∧ (cell12286 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12286 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12286 ⟨31,by decide⟩).lower ∧ (cell12286 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12286 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12286 ⟨32,by decide⟩).lower ∧ (cell12286 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12286 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12286 ⟨33,by decide⟩).lower ∧ (cell12286 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12286 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12286 ⟨34,by decide⟩).lower ∧ (cell12286 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12286 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12286 ⟨35,by decide⟩).lower ∧ (cell12286 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12286 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12286 ⟨36,by decide⟩).lower ∧ (cell12286 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12286 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12286 ⟨37,by decide⟩).lower ∧ (cell12286 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12286 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12286 ⟨38,by decide⟩).lower ∧ (cell12286 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12286 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12286 ⟨39,by decide⟩).lower ∧ (cell12286 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12286 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12286 ⟨40,by decide⟩).lower ∧ (cell12286 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12286 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12286 ⟨41,by decide⟩).lower ∧ (cell12286 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12286 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12286 ⟨42,by decide⟩).lower ∧ (cell12286 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12286 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12286 ⟨43,by decide⟩).lower ∧ (cell12286 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12286 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12286 ⟨44,by decide⟩).lower ∧ (cell12286 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12286 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12286 ⟨45,by decide⟩).lower ∧ (cell12286 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12286 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12286 ⟨46,by decide⟩).lower ∧ (cell12286 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12286 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12286 ⟨47,by decide⟩).lower ∧ (cell12286 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12286 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12286 ⟨48,by decide⟩).lower ∧ (cell12286 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12286 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12286 ⟨49,by decide⟩).lower ∧ (cell12286 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12286 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12286 ⟨50,by decide⟩).lower ∧ (cell12286 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12286 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12286 ⟨51,by decide⟩).lower ∧ (cell12286 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12286 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12286 ⟨52,by decide⟩).lower ∧ (cell12286 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12286 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12286 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12286 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12286,cell12286,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12286 i).lower ∧
    (cell12286 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12286 i).upper ≤ (0.532 : ℝ) ∧
    (cell12286 i).centre ≤ (0.1 : ℝ) ∧ (cell12286 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12286 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12286 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12286

/-! The local source numeric instances at 12286 have no network premises. -/
namespace BstLean.Part264b.N12286
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12286 cell12286)

noncomputable def sourceNumerics12286 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12286 (cell12286 i)
      scalarRow12286.M scalarRow12286.H scalarRow12286.xi := by
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
    energy_allowance := scalarRow12286.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12286]
    centre_nonneg := (scalarRow12286.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12286]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12286
/-! Actual 12287 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12287
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12287 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12287 12287 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12287.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12287 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12287 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12287 := gPlus_lower 12287
end BstLean.Part264b.N12287

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12287
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036411407518 : ℝ) ≤ wn 12287 := by
  have hn : √(12287 : ℝ) ≤ 110.846741043660 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12287 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.846741043660 ≤ 2 / √12287 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000260498638 : ℝ) ≤ rhoBar 12287 BstLean.Part154.csC ∧
    rhoBar 12287 BstLean.Part154.csC ≤ 0.000260522566 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036411407518 : ℝ) / (1.295212 * 12287) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12287) := by gcongr
      _ ≤ (0.000260522566 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12287 BstLean.Part154.csC) ≤ 0.001042158137 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12287 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12287 BstLean.Part154.csC) (piBar (rhoBar 12287 BstLean.Part154.csC)) ≤ 0.000198989211 ∧
    cc1 (rhoBar 12287 BstLean.Part154.csC) (piBar (rhoBar 12287 BstLean.Part154.csC)) ≤ 0.000126618091 ∧
    cc2 (rhoBar 12287 BstLean.Part154.csC) ≤ 0.000073502692 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12287 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12287 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12287 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12287 BstLean.Part154.csC * nuR (rhoBar 12287 BstLean.Part154.csC)) ≤ 0.000521062100 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000260522566 : ℝ) * 0.001042158137 := by gcongr
      _ ≤ (0.000521062100 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12287 BstLean.Part154.csC) * nuR (rhoBar 12287 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001042158137 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12287 BstLean.Part154.csC) * rhoBar 12287 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000260522566 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000260522566 / 2 + 0.399 * 0.001042158137 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198989211 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000521062100 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126618091 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000260522566 / 1.414213562 := by gcongr
      _ ≤ (0.000073502692 : ℝ) := by norm_num

end BstLean.Part264b.N12287

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12287
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12287 BstLean.Part154.csC) (piBar (rhoBar 12287 BstLean.Part154.csC)) ≤ 1.70999E-7 := by
  have hr0 : 0 ≤ rhoBar 12287 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12287 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12287 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12287 BstLean.Part154.csC) (piBar (rhoBar 12287 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12287 BstLean.Part154.csC) (piBar (rhoBar 12287 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12287 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198989211 : ℝ) ^ 2 + 0.000126618091 ^ 2 + 3 * 0.000073502692 ^ 2 +
        2 * 0.797885 * 0.000198989211 * 0.000126618091 + 2 * 0.000198989211 * 0.000073502692 +
        4 * 0.797885 * 0.000126618091 * 0.000073502692 := by gcongr
    _ ≤ (1.70999E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12287 BstLean.Part154.csC Θ ≤ 0.002721569984 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12287 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12287 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12287 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12287 BstLean.Part154.csC) (piBar (rhoBar 12287 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12287 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.70999E-7 / (0.000260498638 : ℝ) := by gcongr
    _ ≤ 0.002721569984 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12287 BstLean.Part154.csC Θ ≤ 0.003021484972 + 0.000687633385 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12287 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12287 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12287 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000260522566 +
        (6863 / 10000) * 0.000260522566 * 12287 * 0.001042158137) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003021484972 + 0.000687633385 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12287 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12287 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12287 0.011 Θ ∧ gammaRatio 12287 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12287 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12287) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12287 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12287 0.011 Θ) :=
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
    badAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12287 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12287 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12287 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12287 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12287 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12287 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12287 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12287 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12287 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12287 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12287 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004121484972 + 0.003409203369 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12287

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12287
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12287 BstLean.Part154.csC) (piBar (rhoBar 12287 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12287 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12287 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12287 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12287 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12287 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12287 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12287 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12287 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12287 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12287 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12287 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12287 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053368737704 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12287) ≤ 0.010773772597 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12287 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010773772597 + 2 * 0.737676 / 12287) := by gcongr
    _ ≤ (0.053368737704 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12287 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12287

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12287
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560484263416 : ℝ) ≤ plow 12287 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12287) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417916741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428824242) : eMP 12287 0.011 xi bn ≤ 0.001229361318 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12287 : ℝ) * (1 - 0.011))) ≤ 0.000607775642 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001428824242 / (12287 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000607775642 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000607775642 : ℝ) + 3.141593 * 0.053417916741 / (12287 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001229361318 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417916741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428824242) : PiBarMP 12287 12 0.011 xi bn ≤ 0.163972845375 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12287 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037799791561 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.235398126010 : ℝ) ≤ √((12287 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.846741043659 : ℝ) ≤ √12287 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12287) ≤ 0.125690734176 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037799791561 + 0.053417916741 * 1.772454 / (2 * (110.235398126010 : ℝ))) * (1 + 0.001229361318) +
        8 / (12287 * 110.846741043659) + 0.125690734176 := by gcongr
    _ ≤ (0.163972845375 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417916741)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428824242) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284491901280) :
    parallelOracle 12287 0.011 xi bn cd ≤ 0.164999635939 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12287 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12287 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560484263416 : ℝ) ≤ plow 12287 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.846741043659 : ℝ) ≤ √12287 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284491901280 : ℝ) / (2 * 0.560484263416 * 110.846741043659)) * 0.163972845375 +
        0.284491901280 ^ 2 / (2 * 0.560484263416 * 110.846741043659) := by gcongr
    _ ≤ (0.164999635939 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053417916741) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001428824242)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284491901280) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12287 12287 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560484263416 : ℝ) ≤ plow 12287 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.846741043659 : ℝ) ≤ √12287 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12287 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12287 Θ 1.22 ≤ 0.011963369311 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.846741043659 := by gcongr <;> linarith
      _ ≤ (0.011963369311 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12287 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12287 12287 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12287 12287 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12287 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12287 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12287 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12287 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164999635939 + 0.011963369311 + (0.008646 : ℝ) *
        (1 + 2 * (0.284491901280 + 0.011963369311) / (0.560484263416 * 110.846741043659))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12287]

end BstLean.Part264b.N12287

/-! The original eight local profiles supply actual 12287 moment certificates. -/
namespace BstLean.Part264b.N12287
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12287 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053417916741 ∧
    0 ≤ bN 12287 BstLean.Part154.csC (groupTheta g) ∧ bN 12287 BstLean.Part154.csC (groupTheta g) ≤ 0.001428824242 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12287 12287 0.011
      (momentAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12287 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12287 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12287 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231123163576 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12287 0.011
      (momentAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12287 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12287
/-! The actual computed-centre upper energy formula at 12287. -/
namespace BstLean.Part264b.N12287
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12287

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12287
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12287 cell12287)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086801945793
  | 2 => 0.087771401470
  | 3 => 0.088743296566
  | 4 => 0.089720006249
  | 5 => 0.090704365992
  | 6 => 0.091699734887
  | 7 => 0.092710064034
  | 8 => 0.093739969879
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12287 12287 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12287 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12287

/-! Actual upper energy certificates on all 43 source endpoints at 12287. -/
namespace BstLean.Part264b.N12287
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12287 cell12287)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12287 (gMinus 12287) (1 - (cell12287 i).lower) ≤ 1 ∧
    energyUpper 12287 (gMinus 12287) (BstLean.Part211.gPlus 12287)
      (finiteEnergy 12287 12287 0.011) (1 - (cell12287 i).lower) ≤
      (cell12287 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12287) (by norm_num)
        (q := 1 - (cell12287 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12287,cell12287]) (by norm_num [scalarRow12287,cell12287])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12287,cell12287])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12287

/-! Source-cell containment and simple scalar guards at 12287. -/
namespace BstLean.Part264b.N12287
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12287 cell12287)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12287 ⟨10,by decide⟩).lower ∧ (cell12287 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12287 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12287 ⟨11,by decide⟩).lower ∧ (cell12287 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12287 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12287 ⟨12,by decide⟩).lower ∧ (cell12287 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12287 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12287 ⟨13,by decide⟩).lower ∧ (cell12287 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12287 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12287 ⟨14,by decide⟩).lower ∧ (cell12287 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12287 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12287 ⟨15,by decide⟩).lower ∧ (cell12287 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12287 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12287 ⟨16,by decide⟩).lower ∧ (cell12287 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12287 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12287 ⟨17,by decide⟩).lower ∧ (cell12287 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12287 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12287 ⟨18,by decide⟩).lower ∧ (cell12287 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12287 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12287 ⟨19,by decide⟩).lower ∧ (cell12287 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12287 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12287 ⟨20,by decide⟩).lower ∧ (cell12287 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12287 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12287 ⟨21,by decide⟩).lower ∧ (cell12287 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12287 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12287 ⟨22,by decide⟩).lower ∧ (cell12287 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12287 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12287 ⟨23,by decide⟩).lower ∧ (cell12287 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12287 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12287 ⟨24,by decide⟩).lower ∧ (cell12287 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12287 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12287 ⟨25,by decide⟩).lower ∧ (cell12287 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12287 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12287 ⟨26,by decide⟩).lower ∧ (cell12287 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12287 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12287 ⟨27,by decide⟩).lower ∧ (cell12287 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12287 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12287 ⟨28,by decide⟩).lower ∧ (cell12287 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12287 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12287 ⟨29,by decide⟩).lower ∧ (cell12287 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12287 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12287 ⟨30,by decide⟩).lower ∧ (cell12287 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12287 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12287 ⟨31,by decide⟩).lower ∧ (cell12287 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12287 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12287 ⟨32,by decide⟩).lower ∧ (cell12287 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12287 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12287 ⟨33,by decide⟩).lower ∧ (cell12287 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12287 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12287 ⟨34,by decide⟩).lower ∧ (cell12287 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12287 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12287 ⟨35,by decide⟩).lower ∧ (cell12287 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12287 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12287 ⟨36,by decide⟩).lower ∧ (cell12287 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12287 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12287 ⟨37,by decide⟩).lower ∧ (cell12287 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12287 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12287 ⟨38,by decide⟩).lower ∧ (cell12287 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12287 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12287 ⟨39,by decide⟩).lower ∧ (cell12287 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12287 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12287 ⟨40,by decide⟩).lower ∧ (cell12287 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12287 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12287 ⟨41,by decide⟩).lower ∧ (cell12287 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12287 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12287 ⟨42,by decide⟩).lower ∧ (cell12287 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12287 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12287 ⟨43,by decide⟩).lower ∧ (cell12287 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12287 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12287 ⟨44,by decide⟩).lower ∧ (cell12287 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12287 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12287 ⟨45,by decide⟩).lower ∧ (cell12287 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12287 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12287 ⟨46,by decide⟩).lower ∧ (cell12287 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12287 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12287 ⟨47,by decide⟩).lower ∧ (cell12287 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12287 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12287 ⟨48,by decide⟩).lower ∧ (cell12287 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12287 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12287 ⟨49,by decide⟩).lower ∧ (cell12287 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12287 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12287 ⟨50,by decide⟩).lower ∧ (cell12287 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12287 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12287 ⟨51,by decide⟩).lower ∧ (cell12287 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12287 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12287 ⟨52,by decide⟩).lower ∧ (cell12287 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12287 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12287 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12287 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12287,cell12287,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12287 i).lower ∧
    (cell12287 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12287 i).upper ≤ (0.532 : ℝ) ∧
    (cell12287 i).centre ≤ (0.1 : ℝ) ∧ (cell12287 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12287 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12287 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12287

/-! The local source numeric instances at 12287 have no network premises. -/
namespace BstLean.Part264b.N12287
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12287 cell12287)

noncomputable def sourceNumerics12287 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12287 (cell12287 i)
      scalarRow12287.M scalarRow12287.H scalarRow12287.xi := by
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
    energy_allowance := scalarRow12287.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12287]
    centre_nonneg := (scalarRow12287.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12287]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12287
/-! Actual 12288 scalar aliases and the unchanged imported parallel allowance. -/
