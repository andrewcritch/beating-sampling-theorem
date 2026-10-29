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
namespace BstLean.Part264b.N12250
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12250 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12250 12250 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12250.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12250 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12250 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12250 := gPlus_lower 12250
end BstLean.Part264b.N12250

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12250
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036466846728 : ℝ) ≤ wn 12250 := by
  have hn : √(12250 : ℝ) ≤ 110.679718105894 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12250 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.679718105894 ≤ 2 / √12250 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261299427 : ℝ) ≤ rhoBar 12250 BstLean.Part154.csC ∧
    rhoBar 12250 BstLean.Part154.csC ≤ 0.000261309450 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036466846728 : ℝ) / (1.295212 * 12250) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12250) := by gcongr
      _ ≤ (0.000261309450 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12250 BstLean.Part154.csC) ≤ 0.001045306083 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12250 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12250 BstLean.Part154.csC) (piBar (rhoBar 12250 BstLean.Part154.csC)) ≤ 0.000199590268 ∧
    cc1 (rhoBar 12250 BstLean.Part154.csC) (piBar (rhoBar 12250 BstLean.Part154.csC)) ≤ 0.000127000541 ∧
    cc2 (rhoBar 12250 BstLean.Part154.csC) ≤ 0.000073724700 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12250 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12250 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12250 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12250 BstLean.Part154.csC * nuR (rhoBar 12250 BstLean.Part154.csC)) ≤ 0.000522635971 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261309450 : ℝ) * 0.001045306083 := by gcongr
      _ ≤ (0.000522635971 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12250 BstLean.Part154.csC) * nuR (rhoBar 12250 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045306083 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12250 BstLean.Part154.csC) * rhoBar 12250 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261309450 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261309450 / 2 + 0.399 * 0.001045306083 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199590268 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522635971 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127000541 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261309450 / 1.414213562 := by gcongr
      _ ≤ (0.000073724700 : ℝ) := by norm_num

end BstLean.Part264b.N12250

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12250
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12250 BstLean.Part154.csC) (piBar (rhoBar 12250 BstLean.Part154.csC)) ≤ 1.72034E-7 := by
  have hr0 : 0 ≤ rhoBar 12250 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12250 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12250 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12250 BstLean.Part154.csC) (piBar (rhoBar 12250 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12250 BstLean.Part154.csC) (piBar (rhoBar 12250 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12250 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199590268 : ℝ) ^ 2 + 0.000127000541 ^ 2 + 3 * 0.000073724700 ^ 2 +
        2 * 0.797885 * 0.000199590268 * 0.000127000541 + 2 * 0.000199590268 * 0.000073724700 +
        4 * 0.797885 * 0.000127000541 * 0.000073724700 := by gcongr
    _ ≤ (1.72034E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12250 BstLean.Part154.csC Θ ≤ 0.002729651622 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12250 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12250 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12250 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12250 BstLean.Part154.csC) (piBar (rhoBar 12250 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12250 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72034E-7 / (0.000261299427 : ℝ) := by gcongr
    _ ≤ 0.002729651622 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12250 BstLean.Part154.csC Θ ≤ 0.003030611673 + 0.000689710317 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12250 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12250 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12250 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261309450 +
        (6863 / 10000) * 0.000261309450 * 12250 * 0.001045306083) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003030611673 + 0.000689710317 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12250 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12250 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12250 0.011 Θ ∧ gammaRatio 12250 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12250 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12250) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12250 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12250 0.011 Θ) :=
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
    badAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12250 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12250 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12250 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12250 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12250 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12250 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12250 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12250 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12250 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12250 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12250 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004130611673 + 0.003419361939 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12250

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12250
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12250 BstLean.Part154.csC) (piBar (rhoBar 12250 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12250 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12250 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12250 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12250 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12250 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12250 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12250 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12250 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12250 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12250 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12250 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12250 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053450163656 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12250) ≤ 0.010790030925 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12250 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010790030925 + 2 * 0.737676 / 12250) := by gcongr
    _ ≤ (0.053450163656 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12250 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12250

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12250
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482470391 : ℝ) ≤ plow 12250 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12250) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053432376691)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433067102) : eMP 12250 0.011 xi bn ≤ 0.001233047285 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12250 : ℝ) * (1 - 0.011))) ≤ 0.000609595895 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001433067102 / (12250 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609595895 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609595895 : ℝ) + 3.141593 * 0.053432376691 / (12250 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001233047285 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053432376691)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433067102) : PiBarMP 12250 12 0.011 xi bn ≤ 0.164219604240 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12250 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037855872755 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.069296354614 : ℝ) ≤ √((12250 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.679718105893 : ℝ) ≤ √12250 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12250) ≤ 0.125880409719 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037855872755 + 0.053432376691 * 1.772454 / (2 * (110.069296354614 : ℝ))) * (1 + 0.001233047285) +
        8 / (12250 * 110.679718105893) + 0.125880409719 := by gcongr
    _ ≤ (0.164219604240 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053432376691)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433067102) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284604607029) :
    parallelOracle 12250 0.011 xi bn cd ≤ 0.165249179571 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12250 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12250 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482470391 : ℝ) ≤ plow 12250 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.679718105893 : ℝ) ≤ √12250 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284604607029 : ℝ) / (2 * 0.560482470391 * 110.679718105893)) * 0.164219604240 +
        0.284604607029 ^ 2 / (2 * 0.560482470391 * 110.679718105893) := by gcongr
    _ ≤ (0.165249179571 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053432376691) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001433067102)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284604607029) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12250 12250 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482470391 : ℝ) ≤ plow 12250 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.679718105893 : ℝ) ≤ √12250 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12250 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12250 Θ 1.22 ≤ 0.011981422818 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.679718105893 := by gcongr <;> linarith
      _ ≤ (0.011981422818 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12250 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12250 12250 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12250 12250 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12250 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12250 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12250 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12250 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165249179571 + 0.011981422818 + (0.008646 : ℝ) *
        (1 + 2 * (0.284604607029 + 0.011981422818) / (0.560482470391 * 110.679718105893))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12250]

end BstLean.Part264b.N12250

/-! The original eight local profiles supply actual 12250 moment certificates. -/
namespace BstLean.Part264b.N12250
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12250 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053432376691 ∧
    0 ≤ bN 12250 BstLean.Part154.csC (groupTheta g) ∧ bN 12250 BstLean.Part154.csC (groupTheta g) ≤ 0.001433067102 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12250 12250 0.011
      (momentAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12250 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12250 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12250 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231154443373 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12250 0.011
      (momentAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12250 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12250
/-! The actual computed-centre upper energy formula at 12250. -/
namespace BstLean.Part264b.N12250
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12250

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12250
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12250 cell12250)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086931756310
  | 2 => 0.087904148872
  | 3 => 0.088879492740
  | 4 => 0.089860273532
  | 5 => 0.090849455364
  | 6 => 0.091850546184
  | 7 => 0.092867668257
  | 8 => 0.093905633644
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12250 12250 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12250 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12250

/-! Actual upper energy certificates on all 43 source endpoints at 12250. -/
namespace BstLean.Part264b.N12250
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12250 cell12250)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12250 (gMinus 12250) (1 - (cell12250 i).lower) ≤ 1 ∧
    energyUpper 12250 (gMinus 12250) (BstLean.Part211.gPlus 12250)
      (finiteEnergy 12250 12250 0.011) (1 - (cell12250 i).lower) ≤
      (cell12250 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12250) (by norm_num)
        (q := 1 - (cell12250 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12250,cell12250]) (by norm_num [scalarRow12250,cell12250])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12250,cell12250])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12250

/-! Source-cell containment and simple scalar guards at 12250. -/
namespace BstLean.Part264b.N12250
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12250 cell12250)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12250 ⟨10,by decide⟩).lower ∧ (cell12250 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12250 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12250 ⟨11,by decide⟩).lower ∧ (cell12250 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12250 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12250 ⟨12,by decide⟩).lower ∧ (cell12250 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12250 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12250 ⟨13,by decide⟩).lower ∧ (cell12250 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12250 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12250 ⟨14,by decide⟩).lower ∧ (cell12250 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12250 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12250 ⟨15,by decide⟩).lower ∧ (cell12250 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12250 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12250 ⟨16,by decide⟩).lower ∧ (cell12250 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12250 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12250 ⟨17,by decide⟩).lower ∧ (cell12250 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12250 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12250 ⟨18,by decide⟩).lower ∧ (cell12250 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12250 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12250 ⟨19,by decide⟩).lower ∧ (cell12250 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12250 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12250 ⟨20,by decide⟩).lower ∧ (cell12250 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12250 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12250 ⟨21,by decide⟩).lower ∧ (cell12250 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12250 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12250 ⟨22,by decide⟩).lower ∧ (cell12250 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12250 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12250 ⟨23,by decide⟩).lower ∧ (cell12250 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12250 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12250 ⟨24,by decide⟩).lower ∧ (cell12250 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12250 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12250 ⟨25,by decide⟩).lower ∧ (cell12250 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12250 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12250 ⟨26,by decide⟩).lower ∧ (cell12250 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12250 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12250 ⟨27,by decide⟩).lower ∧ (cell12250 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12250 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12250 ⟨28,by decide⟩).lower ∧ (cell12250 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12250 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12250 ⟨29,by decide⟩).lower ∧ (cell12250 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12250 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12250 ⟨30,by decide⟩).lower ∧ (cell12250 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12250 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12250 ⟨31,by decide⟩).lower ∧ (cell12250 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12250 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12250 ⟨32,by decide⟩).lower ∧ (cell12250 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12250 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12250 ⟨33,by decide⟩).lower ∧ (cell12250 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12250 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12250 ⟨34,by decide⟩).lower ∧ (cell12250 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12250 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12250 ⟨35,by decide⟩).lower ∧ (cell12250 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12250 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12250 ⟨36,by decide⟩).lower ∧ (cell12250 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12250 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12250 ⟨37,by decide⟩).lower ∧ (cell12250 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12250 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12250 ⟨38,by decide⟩).lower ∧ (cell12250 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12250 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12250 ⟨39,by decide⟩).lower ∧ (cell12250 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12250 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12250 ⟨40,by decide⟩).lower ∧ (cell12250 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12250 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12250 ⟨41,by decide⟩).lower ∧ (cell12250 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12250 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12250 ⟨42,by decide⟩).lower ∧ (cell12250 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12250 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12250 ⟨43,by decide⟩).lower ∧ (cell12250 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12250 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12250 ⟨44,by decide⟩).lower ∧ (cell12250 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12250 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12250 ⟨45,by decide⟩).lower ∧ (cell12250 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12250 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12250 ⟨46,by decide⟩).lower ∧ (cell12250 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12250 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12250 ⟨47,by decide⟩).lower ∧ (cell12250 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12250 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12250 ⟨48,by decide⟩).lower ∧ (cell12250 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12250 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12250 ⟨49,by decide⟩).lower ∧ (cell12250 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12250 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12250 ⟨50,by decide⟩).lower ∧ (cell12250 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12250 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12250 ⟨51,by decide⟩).lower ∧ (cell12250 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12250 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12250 ⟨52,by decide⟩).lower ∧ (cell12250 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12250 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12250 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12250 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12250,cell12250,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12250 i).lower ∧
    (cell12250 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12250 i).upper ≤ (0.532 : ℝ) ∧
    (cell12250 i).centre ≤ (0.1 : ℝ) ∧ (cell12250 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12250 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12250 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12250

/-! The local source numeric instances at 12250 have no network premises. -/
namespace BstLean.Part264b.N12250
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12250 cell12250)

noncomputable def sourceNumerics12250 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12250 (cell12250 i)
      scalarRow12250.M scalarRow12250.H scalarRow12250.xi := by
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
    energy_allowance := scalarRow12250.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12250]
    centre_nonneg := (scalarRow12250.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12250]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12250
/-! Actual 12251 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12251
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12251 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12251 12251 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12251.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12251 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12251 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12251 := gPlus_lower 12251
end BstLean.Part264b.N12251

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12251
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036465345050 : ℝ) ≤ wn 12251 := by
  have hn : √(12251 : ℝ) ≤ 110.684235553217 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12251 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.684235553217 ≤ 2 / √12251 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261277720 : ℝ) ≤ rhoBar 12251 BstLean.Part154.csC ∧
    rhoBar 12251 BstLean.Part154.csC ≤ 0.000261288120 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036465345050 : ℝ) / (1.295212 * 12251) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12251) := by gcongr
      _ ≤ (0.000261288120 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12251 BstLean.Part154.csC) ≤ 0.001045220752 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12251 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12251 BstLean.Part154.csC) (piBar (rhoBar 12251 BstLean.Part154.csC)) ≤ 0.000199573975 ∧
    cc1 (rhoBar 12251 BstLean.Part154.csC) (piBar (rhoBar 12251 BstLean.Part154.csC)) ≤ 0.000126990174 ∧
    cc2 (rhoBar 12251 BstLean.Part154.csC) ≤ 0.000073718683 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12251 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12251 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12251 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12251 BstLean.Part154.csC * nuR (rhoBar 12251 BstLean.Part154.csC)) ≤ 0.000522593308 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261288120 : ℝ) * 0.001045220752 := by gcongr
      _ ≤ (0.000522593308 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12251 BstLean.Part154.csC) * nuR (rhoBar 12251 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045220752 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12251 BstLean.Part154.csC) * rhoBar 12251 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261288120 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261288120 / 2 + 0.399 * 0.001045220752 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199573975 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522593308 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126990174 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261288120 / 1.414213562 := by gcongr
      _ ≤ (0.000073718683 : ℝ) := by norm_num

end BstLean.Part264b.N12251

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12251
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12251 BstLean.Part154.csC) (piBar (rhoBar 12251 BstLean.Part154.csC)) ≤ 1.72006E-7 := by
  have hr0 : 0 ≤ rhoBar 12251 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12251 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12251 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12251 BstLean.Part154.csC) (piBar (rhoBar 12251 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12251 BstLean.Part154.csC) (piBar (rhoBar 12251 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12251 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199573975 : ℝ) ^ 2 + 0.000126990174 ^ 2 + 3 * 0.000073718683 ^ 2 +
        2 * 0.797885 * 0.000199573975 * 0.000126990174 + 2 * 0.000199573975 * 0.000073718683 +
        4 * 0.797885 * 0.000126990174 * 0.000073718683 := by gcongr
    _ ≤ (1.72006E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12251 BstLean.Part154.csC Θ ≤ 0.002729434091 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12251 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12251 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12251 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12251 BstLean.Part154.csC) (piBar (rhoBar 12251 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12251 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.72006E-7 / (0.000261277720 : ℝ) := by gcongr
    _ ≤ 0.002729434091 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12251 BstLean.Part154.csC Θ ≤ 0.003030364272 + 0.000689654017 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12251 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12251 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12251 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261288120 +
        (6863 / 10000) * 0.000261288120 * 12251 * 0.001045220752) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003030364272 + 0.000689654017 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12251 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12251 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12251 0.011 Θ ∧ gammaRatio 12251 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12251 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12251) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12251 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12251 0.011 Θ) :=
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
    badAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12251 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12251 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12251 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12251 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12251 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12251 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12251 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12251 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12251 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12251 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12251 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004130364272 + 0.003419088108 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12251

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12251
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12251 BstLean.Part154.csC) (piBar (rhoBar 12251 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12251 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12251 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12251 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12251 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12251 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12251 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12251 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12251 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12251 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12251 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12251 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12251 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053447958068 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12251) ≤ 0.010789590542 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12251 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010789590542 + 2 * 0.737676 / 12251) := by gcongr
    _ ≤ (0.053447958068 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12251 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12251

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12251
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482518994 : ℝ) ≤ plow 12251 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12251) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431985529)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432952898) : eMP 12251 0.011 xi bn ≤ 0.001232947713 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12251 : ℝ) * (1 - 0.011))) ≤ 0.000609546725 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001432952898 / (12251 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609546725 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609546725 : ℝ) + 3.141593 * 0.053431985529 / (12251 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001232947713 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431985529)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432952898) : PiBarMP 12251 12 0.011 xi bn ≤ 0.164212931016 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12251 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037854364320 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.073788887273 : ℝ) ≤ √((12251 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.684235553216 : ℝ) ≤ √12251 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12251) ≤ 0.125875272058 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037854364320 + 0.053431985529 * 1.772454 / (2 * (110.073788887273 : ℝ))) * (1 + 0.001232947713) +
        8 / (12251 * 110.684235553216) + 0.125875272058 := by gcongr
    _ ≤ (0.164212931016 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431985529)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432952898) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284601555334) :
    parallelOracle 12251 0.011 xi bn cd ≤ 0.165242430891 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12251 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12251 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482518994 : ℝ) ≤ plow 12251 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.684235553216 : ℝ) ≤ √12251 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284601555334 : ℝ) / (2 * 0.560482518994 * 110.684235553216)) * 0.164212931016 +
        0.284601555334 ^ 2 / (2 * 0.560482518994 * 110.684235553216) := by gcongr
    _ ≤ (0.165242430891 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431985529) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432952898)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284601555334) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12251 12251 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482518994 : ℝ) ≤ plow 12251 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.684235553216 : ℝ) ≤ √12251 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12251 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12251 Θ 1.22 ≤ 0.011980933811 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.684235553216 := by gcongr <;> linarith
      _ ≤ (0.011980933811 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12251 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12251 12251 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12251 12251 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12251 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12251 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12251 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12251 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165242430891 + 0.011980933811 + (0.008646 : ℝ) *
        (1 + 2 * (0.284601555334 + 0.011980933811) / (0.560482518994 * 110.684235553216))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12251]

end BstLean.Part264b.N12251

/-! The original eight local profiles supply actual 12251 moment certificates. -/
namespace BstLean.Part264b.N12251
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12251 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053431985529 ∧
    0 ≤ bN 12251 BstLean.Part154.csC (groupTheta g) ∧ bN 12251 BstLean.Part154.csC (groupTheta g) ≤ 0.001432952898 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12251 12251 0.011
      (momentAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12251 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12251 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12251 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231153597266 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12251 0.011
      (momentAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12251 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12251
/-! The actual computed-centre upper energy formula at 12251. -/
namespace BstLean.Part264b.N12251
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12251

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12251
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12251 cell12251)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086928216770
  | 2 => 0.087900528536
  | 3 => 0.088875777445
  | 4 => 0.089856446066
  | 5 => 0.090845494967
  | 6 => 0.091846427993
  | 7 => 0.092863362690
  | 8 => 0.093901105731
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12251 12251 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12251 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12251

/-! Actual upper energy certificates on all 43 source endpoints at 12251. -/
namespace BstLean.Part264b.N12251
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12251 cell12251)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12251 (gMinus 12251) (1 - (cell12251 i).lower) ≤ 1 ∧
    energyUpper 12251 (gMinus 12251) (BstLean.Part211.gPlus 12251)
      (finiteEnergy 12251 12251 0.011) (1 - (cell12251 i).lower) ≤
      (cell12251 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12251) (by norm_num)
        (q := 1 - (cell12251 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12251,cell12251]) (by norm_num [scalarRow12251,cell12251])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12251,cell12251])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12251

/-! Source-cell containment and simple scalar guards at 12251. -/
namespace BstLean.Part264b.N12251
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12251 cell12251)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12251 ⟨10,by decide⟩).lower ∧ (cell12251 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12251 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12251 ⟨11,by decide⟩).lower ∧ (cell12251 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12251 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12251 ⟨12,by decide⟩).lower ∧ (cell12251 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12251 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12251 ⟨13,by decide⟩).lower ∧ (cell12251 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12251 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12251 ⟨14,by decide⟩).lower ∧ (cell12251 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12251 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12251 ⟨15,by decide⟩).lower ∧ (cell12251 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12251 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12251 ⟨16,by decide⟩).lower ∧ (cell12251 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12251 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12251 ⟨17,by decide⟩).lower ∧ (cell12251 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12251 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12251 ⟨18,by decide⟩).lower ∧ (cell12251 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12251 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12251 ⟨19,by decide⟩).lower ∧ (cell12251 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12251 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12251 ⟨20,by decide⟩).lower ∧ (cell12251 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12251 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12251 ⟨21,by decide⟩).lower ∧ (cell12251 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12251 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12251 ⟨22,by decide⟩).lower ∧ (cell12251 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12251 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12251 ⟨23,by decide⟩).lower ∧ (cell12251 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12251 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12251 ⟨24,by decide⟩).lower ∧ (cell12251 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12251 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12251 ⟨25,by decide⟩).lower ∧ (cell12251 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12251 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12251 ⟨26,by decide⟩).lower ∧ (cell12251 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12251 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12251 ⟨27,by decide⟩).lower ∧ (cell12251 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12251 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12251 ⟨28,by decide⟩).lower ∧ (cell12251 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12251 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12251 ⟨29,by decide⟩).lower ∧ (cell12251 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12251 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12251 ⟨30,by decide⟩).lower ∧ (cell12251 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12251 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12251 ⟨31,by decide⟩).lower ∧ (cell12251 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12251 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12251 ⟨32,by decide⟩).lower ∧ (cell12251 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12251 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12251 ⟨33,by decide⟩).lower ∧ (cell12251 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12251 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12251 ⟨34,by decide⟩).lower ∧ (cell12251 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12251 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12251 ⟨35,by decide⟩).lower ∧ (cell12251 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12251 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12251 ⟨36,by decide⟩).lower ∧ (cell12251 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12251 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12251 ⟨37,by decide⟩).lower ∧ (cell12251 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12251 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12251 ⟨38,by decide⟩).lower ∧ (cell12251 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12251 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12251 ⟨39,by decide⟩).lower ∧ (cell12251 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12251 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12251 ⟨40,by decide⟩).lower ∧ (cell12251 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12251 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12251 ⟨41,by decide⟩).lower ∧ (cell12251 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12251 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12251 ⟨42,by decide⟩).lower ∧ (cell12251 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12251 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12251 ⟨43,by decide⟩).lower ∧ (cell12251 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12251 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12251 ⟨44,by decide⟩).lower ∧ (cell12251 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12251 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12251 ⟨45,by decide⟩).lower ∧ (cell12251 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12251 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12251 ⟨46,by decide⟩).lower ∧ (cell12251 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12251 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12251 ⟨47,by decide⟩).lower ∧ (cell12251 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12251 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12251 ⟨48,by decide⟩).lower ∧ (cell12251 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12251 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12251 ⟨49,by decide⟩).lower ∧ (cell12251 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12251 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12251 ⟨50,by decide⟩).lower ∧ (cell12251 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12251 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12251 ⟨51,by decide⟩).lower ∧ (cell12251 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12251 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12251 ⟨52,by decide⟩).lower ∧ (cell12251 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12251 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12251 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12251 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12251,cell12251,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12251 i).lower ∧
    (cell12251 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12251 i).upper ≤ (0.532 : ℝ) ∧
    (cell12251 i).centre ≤ (0.1 : ℝ) ∧ (cell12251 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12251 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12251 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12251

/-! The local source numeric instances at 12251 have no network premises. -/
namespace BstLean.Part264b.N12251
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12251 cell12251)

noncomputable def sourceNumerics12251 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12251 (cell12251 i)
      scalarRow12251.M scalarRow12251.H scalarRow12251.xi := by
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
    energy_allowance := scalarRow12251.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12251]
    centre_nonneg := (scalarRow12251.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12251]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12251
/-! Actual 12252 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12252
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12252 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12252 12252 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12252.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12252 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12252 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12252 := gPlus_lower 12252
end BstLean.Part264b.N12252

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12252
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036463843557 : ℝ) ≤ wn 12252 := by
  have hn : √(12252 : ℝ) ≤ 110.688752816174 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12252 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.688752816174 ≤ 2 / √12252 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261256016 : ℝ) ≤ rhoBar 12252 BstLean.Part154.csC ∧
    rhoBar 12252 BstLean.Part154.csC ≤ 0.000261266794 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036463843557 : ℝ) / (1.295212 * 12252) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12252) := by gcongr
      _ ≤ (0.000261266794 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12252 BstLean.Part154.csC) ≤ 0.001045135437 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12252 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12252 BstLean.Part154.csC) (piBar (rhoBar 12252 BstLean.Part154.csC)) ≤ 0.000199557686 ∧
    cc1 (rhoBar 12252 BstLean.Part154.csC) (piBar (rhoBar 12252 BstLean.Part154.csC)) ≤ 0.000126979809 ∧
    cc2 (rhoBar 12252 BstLean.Part154.csC) ≤ 0.000073712666 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12252 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12252 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12252 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12252 BstLean.Part154.csC * nuR (rhoBar 12252 BstLean.Part154.csC)) ≤ 0.000522550653 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261266794 : ℝ) * 0.001045135437 := by gcongr
      _ ≤ (0.000522550653 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12252 BstLean.Part154.csC) * nuR (rhoBar 12252 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045135437 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12252 BstLean.Part154.csC) * rhoBar 12252 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261266794 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261266794 / 2 + 0.399 * 0.001045135437 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199557686 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522550653 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126979809 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261266794 / 1.414213562 := by gcongr
      _ ≤ (0.000073712666 : ℝ) := by norm_num

end BstLean.Part264b.N12252

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12252
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12252 BstLean.Part154.csC) (piBar (rhoBar 12252 BstLean.Part154.csC)) ≤ 1.71978E-7 := by
  have hr0 : 0 ≤ rhoBar 12252 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12252 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12252 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12252 BstLean.Part154.csC) (piBar (rhoBar 12252 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12252 BstLean.Part154.csC) (piBar (rhoBar 12252 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12252 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199557686 : ℝ) ^ 2 + 0.000126979809 ^ 2 + 3 * 0.000073712666 ^ 2 +
        2 * 0.797885 * 0.000199557686 * 0.000126979809 + 2 * 0.000199557686 * 0.000073712666 +
        4 * 0.797885 * 0.000126979809 * 0.000073712666 := by gcongr
    _ ≤ (1.71978E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12252 BstLean.Part154.csC Θ ≤ 0.002729216493 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12252 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12252 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12252 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12252 BstLean.Part154.csC) (piBar (rhoBar 12252 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12252 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71978E-7 / (0.000261256016 : ℝ) := by gcongr
    _ ≤ 0.002729216493 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12252 BstLean.Part154.csC Θ ≤ 0.003030116924 + 0.000689597729 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12252 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12252 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12252 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261266794 +
        (6863 / 10000) * 0.000261266794 * 12252 * 0.001045135437) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003030116924 + 0.000689597729 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12252 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12252 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12252 0.011 Θ ∧ gammaRatio 12252 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12252 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12252) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12252 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12252 0.011 Θ) :=
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
    badAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12252 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12252 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12252 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12252 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12252 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12252 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12252 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12252 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12252 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12252 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12252 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004130116924 + 0.003418814222 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12252

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12252
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12252 BstLean.Part154.csC) (piBar (rhoBar 12252 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12252 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12252 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12252 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12252 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12252 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12252 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12252 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12252 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12252 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12252 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12252 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12252 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053445752757 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12252) ≤ 0.010789150214 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12252 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010789150214 + 2 * 0.737676 / 12252) := by gcongr
    _ ≤ (0.053445752757 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12252 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12252

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12252
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482567588 : ℝ) ≤ plow 12252 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12252) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431594391)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432838659) : eMP 12252 0.011 xi bn ≤ 0.001232848136 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12252 : ℝ) * (1 - 0.011))) ≤ 0.000609497553 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001432838659 / (12252 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609497553 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609497553 : ℝ) + 3.141593 * 0.053431594391 / (12252 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001232848136 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431594391)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432838659) : PiBarMP 12252 12 0.011 xi bn ≤ 0.164206257900 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12252 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037852855362 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.078281236581 : ℝ) ≤ √((12252 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.688752816173 : ℝ) ≤ √12252 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12252) ≤ 0.125870135026 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037852855362 + 0.053431594391 * 1.772454 / (2 * (110.078281236581 : ℝ))) * (1 + 0.001232848136) +
        8 / (12252 * 110.688752816173) + 0.125870135026 := by gcongr
    _ ≤ (0.164206257900 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431594391)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432838659) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284598503965) :
    parallelOracle 12252 0.011 xi bn cd ≤ 0.165235682329 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12252 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12252 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482567588 : ℝ) ≤ plow 12252 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.688752816173 : ℝ) ≤ √12252 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284598503965 : ℝ) / (2 * 0.560482567588 * 110.688752816173)) * 0.164206257900 +
        0.284598503965 ^ 2 / (2 * 0.560482567588 * 110.688752816173) := by gcongr
    _ ≤ (0.165235682329 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431594391) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432838659)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284598503965) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12252 12252 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482567588 : ℝ) ≤ plow 12252 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.688752816173 : ℝ) ≤ √12252 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12252 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12252 Θ 1.22 ≤ 0.011980444863 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.688752816173 := by gcongr <;> linarith
      _ ≤ (0.011980444863 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12252 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12252 12252 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12252 12252 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12252 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12252 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12252 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12252 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165235682329 + 0.011980444863 + (0.008646 : ℝ) *
        (1 + 2 * (0.284598503965 + 0.011980444863) / (0.560482567588 * 110.688752816173))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12252]

end BstLean.Part264b.N12252

/-! The original eight local profiles supply actual 12252 moment certificates. -/
namespace BstLean.Part264b.N12252
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12252 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053431594391 ∧
    0 ≤ bN 12252 BstLean.Part154.csC (groupTheta g) ∧ bN 12252 BstLean.Part154.csC (groupTheta g) ≤ 0.001432838659 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12252 12252 0.011
      (momentAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12252 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12252 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12252 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231152751208 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12252 0.011
      (momentAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12252 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12252
/-! The actual computed-centre upper energy formula at 12252. -/
namespace BstLean.Part264b.N12252
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12252

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12252
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12252 cell12252)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086924678982
  | 2 => 0.087896910033
  | 3 => 0.088872064081
  | 4 => 0.089852620652
  | 5 => 0.090841536770
  | 6 => 0.091842312179
  | 7 => 0.092859059713
  | 8 => 0.093896580662
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12252 12252 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12252 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12252

/-! Actual upper energy certificates on all 43 source endpoints at 12252. -/
namespace BstLean.Part264b.N12252
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12252 cell12252)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12252 (gMinus 12252) (1 - (cell12252 i).lower) ≤ 1 ∧
    energyUpper 12252 (gMinus 12252) (BstLean.Part211.gPlus 12252)
      (finiteEnergy 12252 12252 0.011) (1 - (cell12252 i).lower) ≤
      (cell12252 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12252) (by norm_num)
        (q := 1 - (cell12252 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12252,cell12252]) (by norm_num [scalarRow12252,cell12252])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12252,cell12252])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12252

/-! Source-cell containment and simple scalar guards at 12252. -/
namespace BstLean.Part264b.N12252
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12252 cell12252)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12252 ⟨10,by decide⟩).lower ∧ (cell12252 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12252 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12252 ⟨11,by decide⟩).lower ∧ (cell12252 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12252 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12252 ⟨12,by decide⟩).lower ∧ (cell12252 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12252 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12252 ⟨13,by decide⟩).lower ∧ (cell12252 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12252 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12252 ⟨14,by decide⟩).lower ∧ (cell12252 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12252 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12252 ⟨15,by decide⟩).lower ∧ (cell12252 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12252 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12252 ⟨16,by decide⟩).lower ∧ (cell12252 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12252 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12252 ⟨17,by decide⟩).lower ∧ (cell12252 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12252 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12252 ⟨18,by decide⟩).lower ∧ (cell12252 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12252 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12252 ⟨19,by decide⟩).lower ∧ (cell12252 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12252 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12252 ⟨20,by decide⟩).lower ∧ (cell12252 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12252 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12252 ⟨21,by decide⟩).lower ∧ (cell12252 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12252 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12252 ⟨22,by decide⟩).lower ∧ (cell12252 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12252 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12252 ⟨23,by decide⟩).lower ∧ (cell12252 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12252 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12252 ⟨24,by decide⟩).lower ∧ (cell12252 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12252 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12252 ⟨25,by decide⟩).lower ∧ (cell12252 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12252 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12252 ⟨26,by decide⟩).lower ∧ (cell12252 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12252 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12252 ⟨27,by decide⟩).lower ∧ (cell12252 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12252 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12252 ⟨28,by decide⟩).lower ∧ (cell12252 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12252 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12252 ⟨29,by decide⟩).lower ∧ (cell12252 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12252 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12252 ⟨30,by decide⟩).lower ∧ (cell12252 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12252 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12252 ⟨31,by decide⟩).lower ∧ (cell12252 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12252 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12252 ⟨32,by decide⟩).lower ∧ (cell12252 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12252 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12252 ⟨33,by decide⟩).lower ∧ (cell12252 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12252 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12252 ⟨34,by decide⟩).lower ∧ (cell12252 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12252 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12252 ⟨35,by decide⟩).lower ∧ (cell12252 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12252 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12252 ⟨36,by decide⟩).lower ∧ (cell12252 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12252 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12252 ⟨37,by decide⟩).lower ∧ (cell12252 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12252 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12252 ⟨38,by decide⟩).lower ∧ (cell12252 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12252 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12252 ⟨39,by decide⟩).lower ∧ (cell12252 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12252 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12252 ⟨40,by decide⟩).lower ∧ (cell12252 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12252 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12252 ⟨41,by decide⟩).lower ∧ (cell12252 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12252 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12252 ⟨42,by decide⟩).lower ∧ (cell12252 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12252 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12252 ⟨43,by decide⟩).lower ∧ (cell12252 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12252 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12252 ⟨44,by decide⟩).lower ∧ (cell12252 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12252 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12252 ⟨45,by decide⟩).lower ∧ (cell12252 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12252 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12252 ⟨46,by decide⟩).lower ∧ (cell12252 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12252 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12252 ⟨47,by decide⟩).lower ∧ (cell12252 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12252 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12252 ⟨48,by decide⟩).lower ∧ (cell12252 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12252 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12252 ⟨49,by decide⟩).lower ∧ (cell12252 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12252 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12252 ⟨50,by decide⟩).lower ∧ (cell12252 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12252 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12252 ⟨51,by decide⟩).lower ∧ (cell12252 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12252 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12252 ⟨52,by decide⟩).lower ∧ (cell12252 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12252 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12252 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12252 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12252,cell12252,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12252 i).lower ∧
    (cell12252 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12252 i).upper ≤ (0.532 : ℝ) ∧
    (cell12252 i).centre ≤ (0.1 : ℝ) ∧ (cell12252 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12252 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12252 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12252

/-! The local source numeric instances at 12252 have no network premises. -/
namespace BstLean.Part264b.N12252
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12252 cell12252)

noncomputable def sourceNumerics12252 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12252 (cell12252 i)
      scalarRow12252.M scalarRow12252.H scalarRow12252.xi := by
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
    energy_allowance := scalarRow12252.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12252]
    centre_nonneg := (scalarRow12252.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12252]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12252
/-! Actual 12253 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12253
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12253 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12253 12253 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12253.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12253 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12253 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12253 := gPlus_lower 12253
end BstLean.Part264b.N12253

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12253
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036462342249 : ℝ) ≤ wn 12253 := by
  have hn : √(12253 : ℝ) ≤ 110.693269894787 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12253 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.693269894787 ≤ 2 / √12253 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261234316 : ℝ) ≤ rhoBar 12253 BstLean.Part154.csC ∧
    rhoBar 12253 BstLean.Part154.csC ≤ 0.000261245472 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036462342249 : ℝ) / (1.295212 * 12253) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12253) := by gcongr
      _ ≤ (0.000261245472 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12253 BstLean.Part154.csC) ≤ 0.001045050138 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12253 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12253 BstLean.Part154.csC) (piBar (rhoBar 12253 BstLean.Part154.csC)) ≤ 0.000199541399 ∧
    cc1 (rhoBar 12253 BstLean.Part154.csC) (piBar (rhoBar 12253 BstLean.Part154.csC)) ≤ 0.000126969446 ∧
    cc2 (rhoBar 12253 BstLean.Part154.csC) ≤ 0.000073706650 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12253 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12253 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12253 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12253 BstLean.Part154.csC * nuR (rhoBar 12253 BstLean.Part154.csC)) ≤ 0.000522508007 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261245472 : ℝ) * 0.001045050138 := by gcongr
      _ ≤ (0.000522508007 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12253 BstLean.Part154.csC) * nuR (rhoBar 12253 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001045050138 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12253 BstLean.Part154.csC) * rhoBar 12253 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261245472 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261245472 / 2 + 0.399 * 0.001045050138 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199541399 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522508007 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126969446 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261245472 / 1.414213562 := by gcongr
      _ ≤ (0.000073706650 : ℝ) := by norm_num

end BstLean.Part264b.N12253

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12253
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12253 BstLean.Part154.csC) (piBar (rhoBar 12253 BstLean.Part154.csC)) ≤ 1.71949E-7 := by
  have hr0 : 0 ≤ rhoBar 12253 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12253 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12253 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12253 BstLean.Part154.csC) (piBar (rhoBar 12253 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12253 BstLean.Part154.csC) (piBar (rhoBar 12253 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12253 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199541399 : ℝ) ^ 2 + 0.000126969446 ^ 2 + 3 * 0.000073706650 ^ 2 +
        2 * 0.797885 * 0.000199541399 * 0.000126969446 + 2 * 0.000199541399 * 0.000073706650 +
        4 * 0.797885 * 0.000126969446 * 0.000073706650 := by gcongr
    _ ≤ (1.71949E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12253 BstLean.Part154.csC Θ ≤ 0.002728982945 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12253 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12253 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12253 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12253 BstLean.Part154.csC) (piBar (rhoBar 12253 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12253 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71949E-7 / (0.000261234316 : ℝ) := by gcongr
    _ ≤ 0.002728982945 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12253 BstLean.Part154.csC Θ ≤ 0.003029869628 + 0.000689541451 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12253 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12253 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12253 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261245472 +
        (6863 / 10000) * 0.000261245472 * 12253 * 0.001045050138) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003029869628 + 0.000689541451 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12253 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12253 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12253 0.011 Θ ∧ gammaRatio 12253 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12253 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12253) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12253 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12253 0.011 Θ) :=
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
    badAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12253 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12253 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12253 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12253 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12253 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12253 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12253 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12253 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12253 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12253 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12253 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004129869628 + 0.003418524396 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12253

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12253
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12253 BstLean.Part154.csC) (piBar (rhoBar 12253 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12253 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12253 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12253 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12253 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12253 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12253 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12253 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12253 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12253 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12253 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12253 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12253 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053443547713 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12253) ≤ 0.010788709939 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12253 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010788709939 + 2 * 0.737676 / 12253) := by gcongr
    _ ≤ (0.053443547713 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12253 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12253

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12253
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482616175 : ℝ) ≤ plow 12253 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12253) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431194936)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432716047) : eMP 12253 0.011 xi bn ≤ 0.001232745002 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12253 : ℝ) * (1 - 0.011))) ≤ 0.000609446603 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001432716047 / (12253 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609446603 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609446603 : ℝ) + 3.141593 * 0.053431194936 / (12253 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001232745002 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431194936)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432716047) : PiBarMP 12253 12 0.011 xi bn ≤ 0.164199474412 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12253 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037851235740 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.082773402562 : ℝ) ≤ √((12253 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.693269894786 : ℝ) ≤ √12253 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12253) ≤ 0.125864998622 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037851235740 + 0.053431194936 * 1.772454 / (2 * (110.082773402562 : ℝ))) * (1 + 0.001232745002) +
        8 / (12253 * 110.693269894786) + 0.125864998622 := by gcongr
    _ ≤ (0.164199474412 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431194936)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432716047) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284595434870) :
    parallelOracle 12253 0.011 xi bn cd ≤ 0.165228823045 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12253 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12253 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482616175 : ℝ) ≤ plow 12253 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.693269894786 : ℝ) ≤ √12253 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284595434870 : ℝ) / (2 * 0.560482616175 * 110.693269894786)) * 0.164199474412 +
        0.284595434870 ^ 2 / (2 * 0.560482616175 * 110.693269894786) := by gcongr
    _ ≤ (0.165228823045 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053431194936) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432716047)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284595434870) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12253 12253 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482616175 : ℝ) ≤ plow 12253 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.693269894786 : ℝ) ≤ √12253 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12253 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12253 Θ 1.22 ≤ 0.011979955975 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.693269894786 := by gcongr <;> linarith
      _ ≤ (0.011979955975 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12253 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12253 12253 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12253 12253 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12253 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12253 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12253 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12253 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165228823045 + 0.011979955975 + (0.008646 : ℝ) *
        (1 + 2 * (0.284595434870 + 0.011979955975) / (0.560482616175 * 110.693269894786))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12253]

end BstLean.Part264b.N12253

/-! The original eight local profiles supply actual 12253 moment certificates. -/
namespace BstLean.Part264b.N12253
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12253 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053431194936 ∧
    0 ≤ bN 12253 BstLean.Part154.csC (groupTheta g) ∧ bN 12253 BstLean.Part154.csC (groupTheta g) ≤ 0.001432716047 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12253 12253 0.011
      (momentAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12253 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12253 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12253 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231151887157 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12253 0.011
      (momentAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12253 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12253
/-! The actual computed-centre upper energy formula at 12253. -/
namespace BstLean.Part264b.N12253
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12253

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12253
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12253 cell12253)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086921142946
  | 2 => 0.087893293361
  | 3 => 0.088868352647
  | 4 => 0.089848797289
  | 5 => 0.090837580769
  | 6 => 0.091838198739
  | 7 => 0.092854759323
  | 8 => 0.093892058435
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12253 12253 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12253 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12253

/-! Actual upper energy certificates on all 43 source endpoints at 12253. -/
namespace BstLean.Part264b.N12253
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12253 cell12253)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12253 (gMinus 12253) (1 - (cell12253 i).lower) ≤ 1 ∧
    energyUpper 12253 (gMinus 12253) (BstLean.Part211.gPlus 12253)
      (finiteEnergy 12253 12253 0.011) (1 - (cell12253 i).lower) ≤
      (cell12253 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12253) (by norm_num)
        (q := 1 - (cell12253 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12253,cell12253]) (by norm_num [scalarRow12253,cell12253])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12253,cell12253])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12253

/-! Source-cell containment and simple scalar guards at 12253. -/
namespace BstLean.Part264b.N12253
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12253 cell12253)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12253 ⟨10,by decide⟩).lower ∧ (cell12253 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12253 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12253 ⟨11,by decide⟩).lower ∧ (cell12253 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12253 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12253 ⟨12,by decide⟩).lower ∧ (cell12253 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12253 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12253 ⟨13,by decide⟩).lower ∧ (cell12253 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12253 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12253 ⟨14,by decide⟩).lower ∧ (cell12253 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12253 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12253 ⟨15,by decide⟩).lower ∧ (cell12253 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12253 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12253 ⟨16,by decide⟩).lower ∧ (cell12253 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12253 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12253 ⟨17,by decide⟩).lower ∧ (cell12253 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12253 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12253 ⟨18,by decide⟩).lower ∧ (cell12253 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12253 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12253 ⟨19,by decide⟩).lower ∧ (cell12253 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12253 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12253 ⟨20,by decide⟩).lower ∧ (cell12253 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12253 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12253 ⟨21,by decide⟩).lower ∧ (cell12253 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12253 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12253 ⟨22,by decide⟩).lower ∧ (cell12253 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12253 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12253 ⟨23,by decide⟩).lower ∧ (cell12253 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12253 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12253 ⟨24,by decide⟩).lower ∧ (cell12253 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12253 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12253 ⟨25,by decide⟩).lower ∧ (cell12253 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12253 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12253 ⟨26,by decide⟩).lower ∧ (cell12253 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12253 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12253 ⟨27,by decide⟩).lower ∧ (cell12253 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12253 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12253 ⟨28,by decide⟩).lower ∧ (cell12253 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12253 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12253 ⟨29,by decide⟩).lower ∧ (cell12253 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12253 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12253 ⟨30,by decide⟩).lower ∧ (cell12253 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12253 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12253 ⟨31,by decide⟩).lower ∧ (cell12253 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12253 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12253 ⟨32,by decide⟩).lower ∧ (cell12253 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12253 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12253 ⟨33,by decide⟩).lower ∧ (cell12253 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12253 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12253 ⟨34,by decide⟩).lower ∧ (cell12253 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12253 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12253 ⟨35,by decide⟩).lower ∧ (cell12253 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12253 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12253 ⟨36,by decide⟩).lower ∧ (cell12253 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12253 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12253 ⟨37,by decide⟩).lower ∧ (cell12253 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12253 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12253 ⟨38,by decide⟩).lower ∧ (cell12253 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12253 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12253 ⟨39,by decide⟩).lower ∧ (cell12253 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12253 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12253 ⟨40,by decide⟩).lower ∧ (cell12253 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12253 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12253 ⟨41,by decide⟩).lower ∧ (cell12253 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12253 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12253 ⟨42,by decide⟩).lower ∧ (cell12253 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12253 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12253 ⟨43,by decide⟩).lower ∧ (cell12253 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12253 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12253 ⟨44,by decide⟩).lower ∧ (cell12253 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12253 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12253 ⟨45,by decide⟩).lower ∧ (cell12253 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12253 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12253 ⟨46,by decide⟩).lower ∧ (cell12253 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12253 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12253 ⟨47,by decide⟩).lower ∧ (cell12253 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12253 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12253 ⟨48,by decide⟩).lower ∧ (cell12253 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12253 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12253 ⟨49,by decide⟩).lower ∧ (cell12253 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12253 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12253 ⟨50,by decide⟩).lower ∧ (cell12253 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12253 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12253 ⟨51,by decide⟩).lower ∧ (cell12253 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12253 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12253 ⟨52,by decide⟩).lower ∧ (cell12253 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12253 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12253 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12253 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12253,cell12253,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12253 i).lower ∧
    (cell12253 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12253 i).upper ≤ (0.532 : ℝ) ∧
    (cell12253 i).centre ≤ (0.1 : ℝ) ∧ (cell12253 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12253 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12253 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12253

/-! The local source numeric instances at 12253 have no network premises. -/
namespace BstLean.Part264b.N12253
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12253 cell12253)

noncomputable def sourceNumerics12253 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12253 (cell12253 i)
      scalarRow12253.M scalarRow12253.H scalarRow12253.xi := by
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
    energy_allowance := scalarRow12253.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12253]
    centre_nonneg := (scalarRow12253.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12253]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12253
/-! Actual 12254 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12254
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12254 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12254 12254 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12254.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12254 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12254 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12254 := gPlus_lower 12254
end BstLean.Part264b.N12254

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12254
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036460841125 : ℝ) ≤ wn 12254 := by
  have hn : √(12254 : ℝ) ≤ 110.697786789078 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12254 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.697786789078 ≤ 2 / √12254 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261212619 : ℝ) ≤ rhoBar 12254 BstLean.Part154.csC ∧
    rhoBar 12254 BstLean.Part154.csC ≤ 0.000261224152 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036460841125 : ℝ) / (1.295212 * 12254) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12254) := by gcongr
      _ ≤ (0.000261224152 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12254 BstLean.Part154.csC) ≤ 0.001044964847 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12254 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12254 BstLean.Part154.csC) (piBar (rhoBar 12254 BstLean.Part154.csC)) ≤ 0.000199525114 ∧
    cc1 (rhoBar 12254 BstLean.Part154.csC) (piBar (rhoBar 12254 BstLean.Part154.csC)) ≤ 0.000126959084 ∧
    cc2 (rhoBar 12254 BstLean.Part154.csC) ≤ 0.000073700635 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12254 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12254 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12254 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12254 BstLean.Part154.csC * nuR (rhoBar 12254 BstLean.Part154.csC)) ≤ 0.000522465364 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261224152 : ℝ) * 0.001044964847 := by gcongr
      _ ≤ (0.000522465364 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12254 BstLean.Part154.csC) * nuR (rhoBar 12254 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044964847 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12254 BstLean.Part154.csC) * rhoBar 12254 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261224152 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261224152 / 2 + 0.399 * 0.001044964847 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199525114 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522465364 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126959084 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261224152 / 1.414213562 := by gcongr
      _ ≤ (0.000073700635 : ℝ) := by norm_num

end BstLean.Part264b.N12254

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12254
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12254 BstLean.Part154.csC) (piBar (rhoBar 12254 BstLean.Part154.csC)) ≤ 1.71921E-7 := by
  have hr0 : 0 ≤ rhoBar 12254 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12254 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12254 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12254 BstLean.Part154.csC) (piBar (rhoBar 12254 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12254 BstLean.Part154.csC) (piBar (rhoBar 12254 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12254 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199525114 : ℝ) ^ 2 + 0.000126959084 ^ 2 + 3 * 0.000073700635 ^ 2 +
        2 * 0.797885 * 0.000199525114 * 0.000126959084 + 2 * 0.000199525114 * 0.000073700635 +
        4 * 0.797885 * 0.000126959084 * 0.000073700635 := by gcongr
    _ ≤ (1.71921E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12254 BstLean.Part154.csC Θ ≤ 0.002728765200 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12254 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12254 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12254 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12254 BstLean.Part154.csC) (piBar (rhoBar 12254 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12254 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71921E-7 / (0.000261212619 : ℝ) := by gcongr
    _ ≤ 0.002728765200 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12254 BstLean.Part154.csC Θ ≤ 0.003029622338 + 0.000689485178 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12254 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12254 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12254 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261224152 +
        (6863 / 10000) * 0.000261224152 * 12254 * 0.001044964847) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003029622338 + 0.000689485178 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12254 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12254 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12254 0.011 Θ ∧ gammaRatio 12254 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12254 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12254) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12254 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12254 0.011 Θ) :=
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
    badAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12254 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12254 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12254 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12254 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12254 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12254 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12254 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12254 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12254 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12254 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12254 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004129622338 + 0.003418250378 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12254

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12254
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12254 BstLean.Part154.csC) (piBar (rhoBar 12254 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12254 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12254 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12254 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12254 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12254 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12254 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12254 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12254 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12254 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12254 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12254 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12254 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053441342942 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12254) ≤ 0.010788269718 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12254 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010788269718 + 2 * 0.737676 / 12254) := by gcongr
    _ ≤ (0.053441342942 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12254 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12254

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12254
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482664754 : ℝ) ≤ plow 12254 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12254) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430803787)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432601730) : eMP 12254 0.011 xi bn ≤ 0.001232645409 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12254 : ℝ) * (1 - 0.011))) ≤ 0.000609397422 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001432601730 / (12254 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609397422 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609397422 : ℝ) + 3.141593 * 0.053430803787 / (12254 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001232645409 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430803787)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432601730) : PiBarMP 12254 12 0.011 xi bn ≤ 0.164192801403 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12254 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037849725627 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.087265385238 : ℝ) ≤ √((12254 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.697786789077 : ℝ) ≤ √12254 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12254) ≤ 0.125859862848 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037849725627 + 0.053430803787 * 1.772454 / (2 * (110.087265385238 : ℝ))) * (1 + 0.001232645409) +
        8 / (12254 * 110.697786789077) + 0.125859862848 := by gcongr
    _ ≤ (0.164192801403 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430803787)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432601730) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284592384011) :
    parallelOracle 12254 0.011 xi bn cd ≤ 0.165222074610 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12254 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12254 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482664754 : ℝ) ≤ plow 12254 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.697786789077 : ℝ) ≤ √12254 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284592384011 : ℝ) / (2 * 0.560482664754 * 110.697786789077)) * 0.164192801403 +
        0.284592384011 ^ 2 / (2 * 0.560482664754 * 110.697786789077) := by gcongr
    _ ≤ (0.165222074610 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430803787) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432601730)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284592384011) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12254 12254 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482664754 : ℝ) ≤ plow 12254 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.697786789077 : ℝ) ≤ √12254 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12254 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12254 Θ 1.22 ≤ 0.011979467147 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.697786789077 := by gcongr <;> linarith
      _ ≤ (0.011979467147 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12254 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12254 12254 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12254 12254 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12254 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12254 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12254 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12254 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165222074610 + 0.011979467147 + (0.008646 : ℝ) *
        (1 + 2 * (0.284592384011 + 0.011979467147) / (0.560482664754 * 110.697786789077))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12254]

end BstLean.Part264b.N12254

/-! The original eight local profiles supply actual 12254 moment certificates. -/
namespace BstLean.Part264b.N12254
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12254 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053430803787 ∧
    0 ≤ bN 12254 BstLean.Part154.csC (groupTheta g) ∧ bN 12254 BstLean.Part154.csC (groupTheta g) ≤ 0.001432601730 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12254 12254 0.011
      (momentAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12254 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12254 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12254 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231151041069 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12254 0.011
      (momentAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12254 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12254
/-! The actual computed-centre upper energy formula at 12254. -/
namespace BstLean.Part264b.N12254
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12254

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12254
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12254 cell12254)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086917608660
  | 2 => 0.087889678518
  | 3 => 0.088864643140
  | 4 => 0.089844975973
  | 5 => 0.090833626963
  | 6 => 0.091834087671
  | 7 => 0.092850461518
  | 8 => 0.093887539047
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12254 12254 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12254 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12254

/-! Actual upper energy certificates on all 43 source endpoints at 12254. -/
namespace BstLean.Part264b.N12254
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12254 cell12254)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12254 (gMinus 12254) (1 - (cell12254 i).lower) ≤ 1 ∧
    energyUpper 12254 (gMinus 12254) (BstLean.Part211.gPlus 12254)
      (finiteEnergy 12254 12254 0.011) (1 - (cell12254 i).lower) ≤
      (cell12254 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12254) (by norm_num)
        (q := 1 - (cell12254 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12254,cell12254]) (by norm_num [scalarRow12254,cell12254])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12254,cell12254])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12254

/-! Source-cell containment and simple scalar guards at 12254. -/
namespace BstLean.Part264b.N12254
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12254 cell12254)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12254 ⟨10,by decide⟩).lower ∧ (cell12254 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12254 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12254 ⟨11,by decide⟩).lower ∧ (cell12254 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12254 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12254 ⟨12,by decide⟩).lower ∧ (cell12254 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12254 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12254 ⟨13,by decide⟩).lower ∧ (cell12254 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12254 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12254 ⟨14,by decide⟩).lower ∧ (cell12254 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12254 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12254 ⟨15,by decide⟩).lower ∧ (cell12254 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12254 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12254 ⟨16,by decide⟩).lower ∧ (cell12254 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12254 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12254 ⟨17,by decide⟩).lower ∧ (cell12254 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12254 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12254 ⟨18,by decide⟩).lower ∧ (cell12254 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12254 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12254 ⟨19,by decide⟩).lower ∧ (cell12254 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12254 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12254 ⟨20,by decide⟩).lower ∧ (cell12254 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12254 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12254 ⟨21,by decide⟩).lower ∧ (cell12254 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12254 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12254 ⟨22,by decide⟩).lower ∧ (cell12254 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12254 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12254 ⟨23,by decide⟩).lower ∧ (cell12254 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12254 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12254 ⟨24,by decide⟩).lower ∧ (cell12254 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12254 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12254 ⟨25,by decide⟩).lower ∧ (cell12254 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12254 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12254 ⟨26,by decide⟩).lower ∧ (cell12254 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12254 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12254 ⟨27,by decide⟩).lower ∧ (cell12254 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12254 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12254 ⟨28,by decide⟩).lower ∧ (cell12254 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12254 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12254 ⟨29,by decide⟩).lower ∧ (cell12254 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12254 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12254 ⟨30,by decide⟩).lower ∧ (cell12254 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12254 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12254 ⟨31,by decide⟩).lower ∧ (cell12254 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12254 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12254 ⟨32,by decide⟩).lower ∧ (cell12254 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12254 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12254 ⟨33,by decide⟩).lower ∧ (cell12254 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12254 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12254 ⟨34,by decide⟩).lower ∧ (cell12254 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12254 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12254 ⟨35,by decide⟩).lower ∧ (cell12254 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12254 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12254 ⟨36,by decide⟩).lower ∧ (cell12254 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12254 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12254 ⟨37,by decide⟩).lower ∧ (cell12254 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12254 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12254 ⟨38,by decide⟩).lower ∧ (cell12254 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12254 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12254 ⟨39,by decide⟩).lower ∧ (cell12254 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12254 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12254 ⟨40,by decide⟩).lower ∧ (cell12254 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12254 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12254 ⟨41,by decide⟩).lower ∧ (cell12254 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12254 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12254 ⟨42,by decide⟩).lower ∧ (cell12254 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12254 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12254 ⟨43,by decide⟩).lower ∧ (cell12254 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12254 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12254 ⟨44,by decide⟩).lower ∧ (cell12254 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12254 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12254 ⟨45,by decide⟩).lower ∧ (cell12254 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12254 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12254 ⟨46,by decide⟩).lower ∧ (cell12254 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12254 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12254 ⟨47,by decide⟩).lower ∧ (cell12254 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12254 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12254 ⟨48,by decide⟩).lower ∧ (cell12254 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12254 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12254 ⟨49,by decide⟩).lower ∧ (cell12254 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12254 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12254 ⟨50,by decide⟩).lower ∧ (cell12254 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12254 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12254 ⟨51,by decide⟩).lower ∧ (cell12254 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12254 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12254 ⟨52,by decide⟩).lower ∧ (cell12254 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12254 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12254 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12254 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12254,cell12254,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12254 i).lower ∧
    (cell12254 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12254 i).upper ≤ (0.532 : ℝ) ∧
    (cell12254 i).centre ≤ (0.1 : ℝ) ∧ (cell12254 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12254 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12254 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12254

/-! The local source numeric instances at 12254 have no network premises. -/
namespace BstLean.Part264b.N12254
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12254 cell12254)

noncomputable def sourceNumerics12254 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12254 (cell12254 i)
      scalarRow12254.M scalarRow12254.H scalarRow12254.xi := by
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
    energy_allowance := scalarRow12254.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12254]
    centre_nonneg := (scalarRow12254.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12254]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12254
/-! Actual 12255 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12255
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12255 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12255 12255 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12255.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12255 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12255 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12255 := gPlus_lower 12255
end BstLean.Part264b.N12255

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12255
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036459340187 : ℝ) ≤ wn 12255 := by
  have hn : √(12255 : ℝ) ≤ 110.702303499070 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12255 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.702303499070 ≤ 2 / √12255 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261190926 : ℝ) ≤ rhoBar 12255 BstLean.Part154.csC ∧
    rhoBar 12255 BstLean.Part154.csC ≤ 0.000261202837 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036459340187 : ℝ) / (1.295212 * 12255) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12255) := by gcongr
      _ ≤ (0.000261202837 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12255 BstLean.Part154.csC) ≤ 0.001044879575 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12255 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12255 BstLean.Part154.csC) (piBar (rhoBar 12255 BstLean.Part154.csC)) ≤ 0.000199508832 ∧
    cc1 (rhoBar 12255 BstLean.Part154.csC) (piBar (rhoBar 12255 BstLean.Part154.csC)) ≤ 0.000126948724 ∧
    cc2 (rhoBar 12255 BstLean.Part154.csC) ≤ 0.000073694621 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12255 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12255 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12255 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12255 BstLean.Part154.csC * nuR (rhoBar 12255 BstLean.Part154.csC)) ≤ 0.000522422731 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261202837 : ℝ) * 0.001044879575 := by gcongr
      _ ≤ (0.000522422731 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12255 BstLean.Part154.csC) * nuR (rhoBar 12255 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044879575 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12255 BstLean.Part154.csC) * rhoBar 12255 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261202837 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261202837 / 2 + 0.399 * 0.001044879575 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199508832 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522422731 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126948724 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261202837 / 1.414213562 := by gcongr
      _ ≤ (0.000073694621 : ℝ) := by norm_num

end BstLean.Part264b.N12255

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12255
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12255 BstLean.Part154.csC) (piBar (rhoBar 12255 BstLean.Part154.csC)) ≤ 1.71893E-7 := by
  have hr0 : 0 ≤ rhoBar 12255 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12255 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12255 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12255 BstLean.Part154.csC) (piBar (rhoBar 12255 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12255 BstLean.Part154.csC) (piBar (rhoBar 12255 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12255 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199508832 : ℝ) ^ 2 + 0.000126948724 ^ 2 + 3 * 0.000073694621 ^ 2 +
        2 * 0.797885 * 0.000199508832 * 0.000126948724 + 2 * 0.000199508832 * 0.000073694621 +
        4 * 0.797885 * 0.000126948724 * 0.000073694621 := by gcongr
    _ ≤ (1.71893E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12255 BstLean.Part154.csC Θ ≤ 0.002728547377 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12255 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12255 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12255 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12255 BstLean.Part154.csC) (piBar (rhoBar 12255 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12255 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71893E-7 / (0.000261190926 : ℝ) := by gcongr
    _ ≤ 0.002728547377 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12255 BstLean.Part154.csC Θ ≤ 0.003029375121 + 0.000689428918 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12255 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12255 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12255 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261202837 +
        (6863 / 10000) * 0.000261202837 * 12255 * 0.001044879575) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003029375121 + 0.000689428918 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12255 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12255 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12255 0.011 Θ ∧ gammaRatio 12255 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12255 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12255) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12255 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12255 0.011 Θ) :=
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
    badAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12255 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12255 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12255 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12255 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12255 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12255 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12255 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12255 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12255 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12255 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12255 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004129375121 + 0.003417976295 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12255

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12255
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12255 BstLean.Part154.csC) (piBar (rhoBar 12255 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12255 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12255 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12255 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12255 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12255 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12255 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12255 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12255 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12255 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12255 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12255 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12255 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053439138448 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12255) ≤ 0.010787829552 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12255 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010787829552 + 2 * 0.737676 / 12255) := by gcongr
    _ ≤ (0.053439138448 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12255 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12255

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12255
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482713325 : ℝ) ≤ plow 12255 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12255) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430412676)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432487373) : eMP 12255 0.011 xi bn ≤ 0.001232545805 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12255 : ℝ) * (1 - 0.011))) ≤ 0.000609348236 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001432487373 / (12255 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609348236 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609348236 : ℝ) + 3.141593 * 0.053430412676 / (12255 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001232545805 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430412676)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432487373) : PiBarMP 12255 12 0.011 xi bn ≤ 0.164186128435 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12255 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037848214925 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.091757184632 : ℝ) ≤ √((12255 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.702303499069 : ℝ) ≤ √12255 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12255) ≤ 0.125854727702 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037848214925 + 0.053430412676 * 1.772454 / (2 * (110.091757184632 : ℝ))) * (1 + 0.001232545805) +
        8 / (12255 * 110.702303499069) + 0.125854727702 := by gcongr
    _ ≤ (0.164186128435 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430412676)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432487373) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284589333508) :
    parallelOracle 12255 0.011 xi bn cd ≤ 0.165215326226 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12255 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12255 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482713325 : ℝ) ≤ plow 12255 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.702303499069 : ℝ) ≤ √12255 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284589333508 : ℝ) / (2 * 0.560482713325 * 110.702303499069)) * 0.164186128435 +
        0.284589333508 ^ 2 / (2 * 0.560482713325 * 110.702303499069) := by gcongr
    _ ≤ (0.165215326226 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430412676) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432487373)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284589333508) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12255 12255 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482713325 : ℝ) ≤ plow 12255 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.702303499069 : ℝ) ≤ √12255 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12255 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12255 Θ 1.22 ≤ 0.011978978378 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.702303499069 := by gcongr <;> linarith
      _ ≤ (0.011978978378 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12255 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12255 12255 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12255 12255 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12255 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12255 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12255 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12255 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165215326226 + 0.011978978378 + (0.008646 : ℝ) *
        (1 + 2 * (0.284589333508 + 0.011978978378) / (0.560482713325 * 110.702303499069))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12255]

end BstLean.Part264b.N12255

/-! The original eight local profiles supply actual 12255 moment certificates. -/
namespace BstLean.Part264b.N12255
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12255 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053430412676 ∧
    0 ≤ bN 12255 BstLean.Part154.csC (groupTheta g) ∧ bN 12255 BstLean.Part154.csC (groupTheta g) ≤ 0.001432487373 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12255 12255 0.011
      (momentAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12255 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12255 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12255 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231150195060 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12255 0.011
      (momentAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12255 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12255
/-! The actual computed-centre upper energy formula at 12255. -/
namespace BstLean.Part264b.N12255
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12255

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12255
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12255 cell12255)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086914076120
  | 2 => 0.087886065502
  | 3 => 0.088860935559
  | 4 => 0.089841156704
  | 5 => 0.090829675349
  | 6 => 0.091829978971
  | 7 => 0.092846166293
  | 8 => 0.093883022494
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12255 12255 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12255 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12255

/-! Actual upper energy certificates on all 43 source endpoints at 12255. -/
namespace BstLean.Part264b.N12255
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12255 cell12255)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12255 (gMinus 12255) (1 - (cell12255 i).lower) ≤ 1 ∧
    energyUpper 12255 (gMinus 12255) (BstLean.Part211.gPlus 12255)
      (finiteEnergy 12255 12255 0.011) (1 - (cell12255 i).lower) ≤
      (cell12255 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12255) (by norm_num)
        (q := 1 - (cell12255 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12255,cell12255]) (by norm_num [scalarRow12255,cell12255])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12255,cell12255])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12255

/-! Source-cell containment and simple scalar guards at 12255. -/
namespace BstLean.Part264b.N12255
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12255 cell12255)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12255 ⟨10,by decide⟩).lower ∧ (cell12255 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12255 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12255 ⟨11,by decide⟩).lower ∧ (cell12255 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12255 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12255 ⟨12,by decide⟩).lower ∧ (cell12255 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12255 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12255 ⟨13,by decide⟩).lower ∧ (cell12255 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12255 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12255 ⟨14,by decide⟩).lower ∧ (cell12255 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12255 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12255 ⟨15,by decide⟩).lower ∧ (cell12255 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12255 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12255 ⟨16,by decide⟩).lower ∧ (cell12255 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12255 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12255 ⟨17,by decide⟩).lower ∧ (cell12255 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12255 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12255 ⟨18,by decide⟩).lower ∧ (cell12255 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12255 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12255 ⟨19,by decide⟩).lower ∧ (cell12255 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12255 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12255 ⟨20,by decide⟩).lower ∧ (cell12255 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12255 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12255 ⟨21,by decide⟩).lower ∧ (cell12255 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12255 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12255 ⟨22,by decide⟩).lower ∧ (cell12255 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12255 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12255 ⟨23,by decide⟩).lower ∧ (cell12255 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12255 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12255 ⟨24,by decide⟩).lower ∧ (cell12255 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12255 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12255 ⟨25,by decide⟩).lower ∧ (cell12255 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12255 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12255 ⟨26,by decide⟩).lower ∧ (cell12255 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12255 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12255 ⟨27,by decide⟩).lower ∧ (cell12255 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12255 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12255 ⟨28,by decide⟩).lower ∧ (cell12255 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12255 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12255 ⟨29,by decide⟩).lower ∧ (cell12255 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12255 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12255 ⟨30,by decide⟩).lower ∧ (cell12255 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12255 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12255 ⟨31,by decide⟩).lower ∧ (cell12255 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12255 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12255 ⟨32,by decide⟩).lower ∧ (cell12255 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12255 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12255 ⟨33,by decide⟩).lower ∧ (cell12255 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12255 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12255 ⟨34,by decide⟩).lower ∧ (cell12255 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12255 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12255 ⟨35,by decide⟩).lower ∧ (cell12255 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12255 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12255 ⟨36,by decide⟩).lower ∧ (cell12255 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12255 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12255 ⟨37,by decide⟩).lower ∧ (cell12255 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12255 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12255 ⟨38,by decide⟩).lower ∧ (cell12255 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12255 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12255 ⟨39,by decide⟩).lower ∧ (cell12255 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12255 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12255 ⟨40,by decide⟩).lower ∧ (cell12255 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12255 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12255 ⟨41,by decide⟩).lower ∧ (cell12255 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12255 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12255 ⟨42,by decide⟩).lower ∧ (cell12255 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12255 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12255 ⟨43,by decide⟩).lower ∧ (cell12255 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12255 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12255 ⟨44,by decide⟩).lower ∧ (cell12255 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12255 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12255 ⟨45,by decide⟩).lower ∧ (cell12255 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12255 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12255 ⟨46,by decide⟩).lower ∧ (cell12255 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12255 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12255 ⟨47,by decide⟩).lower ∧ (cell12255 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12255 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12255 ⟨48,by decide⟩).lower ∧ (cell12255 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12255 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12255 ⟨49,by decide⟩).lower ∧ (cell12255 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12255 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12255 ⟨50,by decide⟩).lower ∧ (cell12255 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12255 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12255 ⟨51,by decide⟩).lower ∧ (cell12255 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12255 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12255 ⟨52,by decide⟩).lower ∧ (cell12255 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12255 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12255 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12255 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12255,cell12255,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12255 i).lower ∧
    (cell12255 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12255 i).upper ≤ (0.532 : ℝ) ∧
    (cell12255 i).centre ≤ (0.1 : ℝ) ∧ (cell12255 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12255 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12255 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12255

/-! The local source numeric instances at 12255 have no network premises. -/
namespace BstLean.Part264b.N12255
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12255 cell12255)

noncomputable def sourceNumerics12255 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12255 (cell12255 i)
      scalarRow12255.M scalarRow12255.H scalarRow12255.xi := by
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
    energy_allowance := scalarRow12255.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12255]
    centre_nonneg := (scalarRow12255.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12255]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12255
/-! Actual 12256 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12256
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12256 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12256 12256 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12256.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12256 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12256 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12256 := gPlus_lower 12256
end BstLean.Part264b.N12256

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12256
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036457839433 : ℝ) ≤ wn 12256 := by
  have hn : √(12256 : ℝ) ≤ 110.706820024785 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12256 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.706820024785 ≤ 2 / √12256 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261169237 : ℝ) ≤ rhoBar 12256 BstLean.Part154.csC ∧
    rhoBar 12256 BstLean.Part154.csC ≤ 0.000261181524 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036457839433 : ℝ) / (1.295212 * 12256) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12256) := by gcongr
      _ ≤ (0.000261181524 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12256 BstLean.Part154.csC) ≤ 0.001044794312 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12256 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12256 BstLean.Part154.csC) (piBar (rhoBar 12256 BstLean.Part154.csC)) ≤ 0.000199492553 ∧
    cc1 (rhoBar 12256 BstLean.Part154.csC) (piBar (rhoBar 12256 BstLean.Part154.csC)) ≤ 0.000126938365 ∧
    cc2 (rhoBar 12256 BstLean.Part154.csC) ≤ 0.000073688608 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12256 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12256 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12256 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12256 BstLean.Part154.csC * nuR (rhoBar 12256 BstLean.Part154.csC)) ≤ 0.000522380102 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261181524 : ℝ) * 0.001044794312 := by gcongr
      _ ≤ (0.000522380102 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12256 BstLean.Part154.csC) * nuR (rhoBar 12256 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044794312 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12256 BstLean.Part154.csC) * rhoBar 12256 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261181524 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261181524 / 2 + 0.399 * 0.001044794312 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199492553 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522380102 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126938365 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261181524 / 1.414213562 := by gcongr
      _ ≤ (0.000073688608 : ℝ) := by norm_num

end BstLean.Part264b.N12256

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12256
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12256 BstLean.Part154.csC) (piBar (rhoBar 12256 BstLean.Part154.csC)) ≤ 1.71865E-7 := by
  have hr0 : 0 ≤ rhoBar 12256 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12256 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12256 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12256 BstLean.Part154.csC) (piBar (rhoBar 12256 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12256 BstLean.Part154.csC) (piBar (rhoBar 12256 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12256 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199492553 : ℝ) ^ 2 + 0.000126938365 ^ 2 + 3 * 0.000073688608 ^ 2 +
        2 * 0.797885 * 0.000199492553 * 0.000126938365 + 2 * 0.000199492553 * 0.000073688608 +
        4 * 0.797885 * 0.000126938365 * 0.000073688608 := by gcongr
    _ ≤ (1.71865E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12256 BstLean.Part154.csC Θ ≤ 0.002728329476 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12256 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12256 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12256 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12256 BstLean.Part154.csC) (piBar (rhoBar 12256 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12256 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71865E-7 / (0.000261169237 : ℝ) := by gcongr
    _ ≤ 0.002728329476 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12256 BstLean.Part154.csC Θ ≤ 0.003029127913 + 0.000689372664 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12256 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12256 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12256 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261181524 +
        (6863 / 10000) * 0.000261181524 * 12256 * 0.001044794312) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003029127913 + 0.000689372664 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12256 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12256 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12256 0.011 Θ ∧ gammaRatio 12256 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12256 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12256) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12256 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12256 0.011 Θ) :=
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
    badAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12256 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12256 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12256 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12256 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12256 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12256 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12256 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12256 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12256 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12256 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12256 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004129127913 + 0.003417702140 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12256

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12256
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12256 BstLean.Part154.csC) (piBar (rhoBar 12256 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12256 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12256 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12256 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12256 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12256 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12256 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12256 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12256 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12256 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12256 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12256 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12256 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053436934222 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12256) ≤ 0.010787389439 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12256 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010787389439 + 2 * 0.737676 / 12256) := by gcongr
    _ ≤ (0.053436934222 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12256 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12256

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12256
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482761888 : ℝ) ≤ plow 12256 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12256) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430021537)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432372975) : eMP 12256 0.011 xi bn ≤ 0.001232446194 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12256 : ℝ) * (1 - 0.011))) ≤ 0.000609299046 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001432372975 / (12256 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609299046 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609299046 : ℝ) + 3.141593 * 0.053430021537 / (12256 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001232446194 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430021537)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432372975) : PiBarMP 12256 12 0.011 xi bn ≤ 0.164179455495 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12256 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037846703622 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.096248800765 : ℝ) ≤ √((12256 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.706820024784 : ℝ) ≤ √12256 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12256) ≤ 0.125849593184 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037846703622 + 0.053430021537 * 1.772454 / (2 * (110.096248800765 : ℝ))) * (1 + 0.001232446194) +
        8 / (12256 * 110.706820024784) + 0.125849593184 := by gcongr
    _ ≤ (0.164179455495 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430021537)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432372975) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284586283209) :
    parallelOracle 12256 0.011 xi bn cd ≤ 0.165208577880 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12256 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12256 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482761888 : ℝ) ≤ plow 12256 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.706820024784 : ℝ) ≤ √12256 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284586283209 : ℝ) / (2 * 0.560482761888 * 110.706820024784)) * 0.164179455495 +
        0.284586283209 ^ 2 / (2 * 0.560482761888 * 110.706820024784) := by gcongr
    _ ≤ (0.165208577880 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053430021537) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432372975)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284586283209) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12256 12256 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482761888 : ℝ) ≤ plow 12256 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.706820024784 : ℝ) ≤ √12256 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12256 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12256 Θ 1.22 ≤ 0.011978489670 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.706820024784 := by gcongr <;> linarith
      _ ≤ (0.011978489670 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12256 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12256 12256 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12256 12256 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12256 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12256 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12256 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12256 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165208577880 + 0.011978489670 + (0.008646 : ℝ) *
        (1 + 2 * (0.284586283209 + 0.011978489670) / (0.560482761888 * 110.706820024784))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12256]

end BstLean.Part264b.N12256

/-! The original eight local profiles supply actual 12256 moment certificates. -/
namespace BstLean.Part264b.N12256
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12256 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053430021537 ∧
    0 ≤ bN 12256 BstLean.Part154.csC (groupTheta g) ∧ bN 12256 BstLean.Part154.csC (groupTheta g) ≤ 0.001432372975 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12256 12256 0.011
      (momentAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12256 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12256 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12256 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231149348987 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12256 0.011
      (momentAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12256 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12256
/-! The actual computed-centre upper energy formula at 12256. -/
namespace BstLean.Part264b.N12256
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12256

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12256
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12256 cell12256)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086910545326
  | 2 => 0.087882454312
  | 3 => 0.088857229901
  | 4 => 0.089837339477
  | 5 => 0.090825725925
  | 6 => 0.091825872637
  | 7 => 0.092841873647
  | 8 => 0.093878508772
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12256 12256 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12256 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12256

/-! Actual upper energy certificates on all 43 source endpoints at 12256. -/
namespace BstLean.Part264b.N12256
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12256 cell12256)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12256 (gMinus 12256) (1 - (cell12256 i).lower) ≤ 1 ∧
    energyUpper 12256 (gMinus 12256) (BstLean.Part211.gPlus 12256)
      (finiteEnergy 12256 12256 0.011) (1 - (cell12256 i).lower) ≤
      (cell12256 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12256) (by norm_num)
        (q := 1 - (cell12256 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12256,cell12256]) (by norm_num [scalarRow12256,cell12256])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12256,cell12256])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12256

/-! Source-cell containment and simple scalar guards at 12256. -/
namespace BstLean.Part264b.N12256
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12256 cell12256)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12256 ⟨10,by decide⟩).lower ∧ (cell12256 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12256 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12256 ⟨11,by decide⟩).lower ∧ (cell12256 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12256 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12256 ⟨12,by decide⟩).lower ∧ (cell12256 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12256 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12256 ⟨13,by decide⟩).lower ∧ (cell12256 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12256 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12256 ⟨14,by decide⟩).lower ∧ (cell12256 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12256 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12256 ⟨15,by decide⟩).lower ∧ (cell12256 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12256 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12256 ⟨16,by decide⟩).lower ∧ (cell12256 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12256 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12256 ⟨17,by decide⟩).lower ∧ (cell12256 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12256 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12256 ⟨18,by decide⟩).lower ∧ (cell12256 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12256 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12256 ⟨19,by decide⟩).lower ∧ (cell12256 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12256 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12256 ⟨20,by decide⟩).lower ∧ (cell12256 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12256 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12256 ⟨21,by decide⟩).lower ∧ (cell12256 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12256 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12256 ⟨22,by decide⟩).lower ∧ (cell12256 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12256 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12256 ⟨23,by decide⟩).lower ∧ (cell12256 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12256 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12256 ⟨24,by decide⟩).lower ∧ (cell12256 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12256 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12256 ⟨25,by decide⟩).lower ∧ (cell12256 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12256 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12256 ⟨26,by decide⟩).lower ∧ (cell12256 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12256 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12256 ⟨27,by decide⟩).lower ∧ (cell12256 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12256 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12256 ⟨28,by decide⟩).lower ∧ (cell12256 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12256 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12256 ⟨29,by decide⟩).lower ∧ (cell12256 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12256 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12256 ⟨30,by decide⟩).lower ∧ (cell12256 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12256 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12256 ⟨31,by decide⟩).lower ∧ (cell12256 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12256 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12256 ⟨32,by decide⟩).lower ∧ (cell12256 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12256 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12256 ⟨33,by decide⟩).lower ∧ (cell12256 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12256 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12256 ⟨34,by decide⟩).lower ∧ (cell12256 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12256 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12256 ⟨35,by decide⟩).lower ∧ (cell12256 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12256 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12256 ⟨36,by decide⟩).lower ∧ (cell12256 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12256 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12256 ⟨37,by decide⟩).lower ∧ (cell12256 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12256 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12256 ⟨38,by decide⟩).lower ∧ (cell12256 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12256 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12256 ⟨39,by decide⟩).lower ∧ (cell12256 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12256 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12256 ⟨40,by decide⟩).lower ∧ (cell12256 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12256 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12256 ⟨41,by decide⟩).lower ∧ (cell12256 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12256 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12256 ⟨42,by decide⟩).lower ∧ (cell12256 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12256 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12256 ⟨43,by decide⟩).lower ∧ (cell12256 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12256 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12256 ⟨44,by decide⟩).lower ∧ (cell12256 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12256 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12256 ⟨45,by decide⟩).lower ∧ (cell12256 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12256 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12256 ⟨46,by decide⟩).lower ∧ (cell12256 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12256 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12256 ⟨47,by decide⟩).lower ∧ (cell12256 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12256 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12256 ⟨48,by decide⟩).lower ∧ (cell12256 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12256 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12256 ⟨49,by decide⟩).lower ∧ (cell12256 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12256 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12256 ⟨50,by decide⟩).lower ∧ (cell12256 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12256 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12256 ⟨51,by decide⟩).lower ∧ (cell12256 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12256 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12256 ⟨52,by decide⟩).lower ∧ (cell12256 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12256 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12256 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12256 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12256,cell12256,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12256 i).lower ∧
    (cell12256 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12256 i).upper ≤ (0.532 : ℝ) ∧
    (cell12256 i).centre ≤ (0.1 : ℝ) ∧ (cell12256 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12256 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12256 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12256

/-! The local source numeric instances at 12256 have no network premises. -/
namespace BstLean.Part264b.N12256
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12256 cell12256)

noncomputable def sourceNumerics12256 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12256 (cell12256 i)
      scalarRow12256.M scalarRow12256.H scalarRow12256.xi := by
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
    energy_allowance := scalarRow12256.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12256]
    centre_nonneg := (scalarRow12256.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12256]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12256
/-! Actual 12257 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12257
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12257 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12257 12257 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12257.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12257 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12257 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12257 := gPlus_lower 12257
end BstLean.Part264b.N12257

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12257
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036456338864 : ℝ) ≤ wn 12257 := by
  have hn : √(12257 : ℝ) ≤ 110.711336366246 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12257 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.711336366246 ≤ 2 / √12257 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261147551 : ℝ) ≤ rhoBar 12257 BstLean.Part154.csC ∧
    rhoBar 12257 BstLean.Part154.csC ≤ 0.000261160216 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036456338864 : ℝ) / (1.295212 * 12257) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12257) := by gcongr
      _ ≤ (0.000261160216 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12257 BstLean.Part154.csC) ≤ 0.001044709069 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12257 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12257 BstLean.Part154.csC) (piBar (rhoBar 12257 BstLean.Part154.csC)) ≤ 0.000199476277 ∧
    cc1 (rhoBar 12257 BstLean.Part154.csC) (piBar (rhoBar 12257 BstLean.Part154.csC)) ≤ 0.000126928009 ∧
    cc2 (rhoBar 12257 BstLean.Part154.csC) ≤ 0.000073682596 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12257 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12257 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12257 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12257 BstLean.Part154.csC * nuR (rhoBar 12257 BstLean.Part154.csC)) ≤ 0.000522337483 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261160216 : ℝ) * 0.001044709069 := by gcongr
      _ ≤ (0.000522337483 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12257 BstLean.Part154.csC) * nuR (rhoBar 12257 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044709069 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12257 BstLean.Part154.csC) * rhoBar 12257 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261160216 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261160216 / 2 + 0.399 * 0.001044709069 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199476277 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522337483 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126928009 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261160216 / 1.414213562 := by gcongr
      _ ≤ (0.000073682596 : ℝ) := by norm_num

end BstLean.Part264b.N12257

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12257
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12257 BstLean.Part154.csC) (piBar (rhoBar 12257 BstLean.Part154.csC)) ≤ 1.71837E-7 := by
  have hr0 : 0 ≤ rhoBar 12257 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12257 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12257 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12257 BstLean.Part154.csC) (piBar (rhoBar 12257 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12257 BstLean.Part154.csC) (piBar (rhoBar 12257 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12257 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199476277 : ℝ) ^ 2 + 0.000126928009 ^ 2 + 3 * 0.000073682596 ^ 2 +
        2 * 0.797885 * 0.000199476277 * 0.000126928009 + 2 * 0.000199476277 * 0.000073682596 +
        4 * 0.797885 * 0.000126928009 * 0.000073682596 := by gcongr
    _ ≤ (1.71837E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12257 BstLean.Part154.csC Θ ≤ 0.002728111507 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12257 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12257 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12257 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12257 BstLean.Part154.csC) (piBar (rhoBar 12257 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12257 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71837E-7 / (0.000261147551 : ℝ) := by gcongr
    _ ≤ 0.002728111507 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12257 BstLean.Part154.csC Θ ≤ 0.003028880780 + 0.000689316423 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12257 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12257 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12257 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261160216 +
        (6863 / 10000) * 0.000261160216 * 12257 * 0.001044709069) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003028880780 + 0.000689316423 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12257 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12257 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12257 0.011 Θ ∧ gammaRatio 12257 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12257 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12257) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12257 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12257 0.011 Θ) :=
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
    badAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12257 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12257 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12257 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12257 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12257 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12257 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12257 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12257 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12257 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12257 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12257 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004128880780 + 0.003417427930 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12257

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12257
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12257 BstLean.Part154.csC) (piBar (rhoBar 12257 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12257 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12257 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12257 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12257 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12257 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12257 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12257 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12257 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12257 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12257 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12257 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12257 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053434730263 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12257) ≤ 0.010786949379 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12257 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010786949379 + 2 * 0.737676 / 12257) := by gcongr
    _ ≤ (0.053434730263 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12257 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12257

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12257
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482810443 : ℝ) ≤ plow 12257 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12257) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053429630444)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432258542) : eMP 12257 0.011 xi bn ≤ 0.001232346574 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12257 : ℝ) * (1 - 0.011))) ≤ 0.000609249852 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001432258542 / (12257 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609249852 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609249852 : ℝ) + 3.141593 * 0.053429630444 / (12257 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001232346574 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053429630444)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432258542) : PiBarMP 12257 12 0.011 xi bn ≤ 0.164172782663 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12257 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037845191795 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.100740233660 : ℝ) ≤ √((12257 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.711336366245 : ℝ) ≤ √12257 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12257) ≤ 0.125844459295 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037845191795 + 0.053429630444 * 1.772454 / (2 * (110.100740233660 : ℝ))) * (1 + 0.001232346574) +
        8 / (12257 * 110.711336366245) + 0.125844459295 := by gcongr
    _ ≤ (0.164172782663 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053429630444)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432258542) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284583233274) :
    parallelOracle 12257 0.011 xi bn cd ≤ 0.165201829653 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12257 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12257 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482810443 : ℝ) ≤ plow 12257 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.711336366245 : ℝ) ≤ √12257 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284583233274 : ℝ) / (2 * 0.560482810443 * 110.711336366245)) * 0.164172782663 +
        0.284583233274 ^ 2 / (2 * 0.560482810443 * 110.711336366245) := by gcongr
    _ ≤ (0.165201829653 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053429630444) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432258542)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284583233274) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12257 12257 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482810443 : ℝ) ≤ plow 12257 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.711336366245 : ℝ) ≤ √12257 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12257 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12257 Θ 1.22 ≤ 0.011978001021 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.711336366245 := by gcongr <;> linarith
      _ ≤ (0.011978001021 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12257 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12257 12257 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12257 12257 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12257 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12257 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12257 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12257 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165201829653 + 0.011978001021 + (0.008646 : ℝ) *
        (1 + 2 * (0.284583233274 + 0.011978001021) / (0.560482810443 * 110.711336366245))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12257]

end BstLean.Part264b.N12257

/-! The original eight local profiles supply actual 12257 moment certificates. -/
namespace BstLean.Part264b.N12257
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12257 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053429630444 ∧
    0 ≤ bN 12257 BstLean.Part154.csC (groupTheta g) ∧ bN 12257 BstLean.Part154.csC (groupTheta g) ≤ 0.001432258542 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12257 12257 0.011
      (momentAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12257 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12257 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12257 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231148503011 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12257 0.011
      (momentAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12257 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12257
/-! The actual computed-centre upper energy formula at 12257. -/
namespace BstLean.Part264b.N12257
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12257

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12257
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12257 cell12257)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086907016275
  | 2 => 0.087878844944
  | 3 => 0.088853526164
  | 4 => 0.089833524292
  | 5 => 0.090821778687
  | 6 => 0.091821768666
  | 7 => 0.092837583576
  | 8 => 0.093873997878
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12257 12257 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12257 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12257

/-! Actual upper energy certificates on all 43 source endpoints at 12257. -/
namespace BstLean.Part264b.N12257
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12257 cell12257)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12257 (gMinus 12257) (1 - (cell12257 i).lower) ≤ 1 ∧
    energyUpper 12257 (gMinus 12257) (BstLean.Part211.gPlus 12257)
      (finiteEnergy 12257 12257 0.011) (1 - (cell12257 i).lower) ≤
      (cell12257 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12257) (by norm_num)
        (q := 1 - (cell12257 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12257,cell12257]) (by norm_num [scalarRow12257,cell12257])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12257,cell12257])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12257

/-! Source-cell containment and simple scalar guards at 12257. -/
namespace BstLean.Part264b.N12257
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12257 cell12257)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12257 ⟨10,by decide⟩).lower ∧ (cell12257 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12257 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12257 ⟨11,by decide⟩).lower ∧ (cell12257 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12257 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12257 ⟨12,by decide⟩).lower ∧ (cell12257 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12257 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12257 ⟨13,by decide⟩).lower ∧ (cell12257 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12257 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12257 ⟨14,by decide⟩).lower ∧ (cell12257 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12257 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12257 ⟨15,by decide⟩).lower ∧ (cell12257 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12257 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12257 ⟨16,by decide⟩).lower ∧ (cell12257 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12257 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12257 ⟨17,by decide⟩).lower ∧ (cell12257 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12257 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12257 ⟨18,by decide⟩).lower ∧ (cell12257 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12257 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12257 ⟨19,by decide⟩).lower ∧ (cell12257 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12257 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12257 ⟨20,by decide⟩).lower ∧ (cell12257 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12257 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12257 ⟨21,by decide⟩).lower ∧ (cell12257 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12257 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12257 ⟨22,by decide⟩).lower ∧ (cell12257 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12257 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12257 ⟨23,by decide⟩).lower ∧ (cell12257 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12257 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12257 ⟨24,by decide⟩).lower ∧ (cell12257 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12257 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12257 ⟨25,by decide⟩).lower ∧ (cell12257 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12257 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12257 ⟨26,by decide⟩).lower ∧ (cell12257 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12257 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12257 ⟨27,by decide⟩).lower ∧ (cell12257 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12257 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12257 ⟨28,by decide⟩).lower ∧ (cell12257 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12257 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12257 ⟨29,by decide⟩).lower ∧ (cell12257 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12257 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12257 ⟨30,by decide⟩).lower ∧ (cell12257 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12257 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12257 ⟨31,by decide⟩).lower ∧ (cell12257 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12257 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12257 ⟨32,by decide⟩).lower ∧ (cell12257 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12257 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12257 ⟨33,by decide⟩).lower ∧ (cell12257 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12257 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12257 ⟨34,by decide⟩).lower ∧ (cell12257 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12257 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12257 ⟨35,by decide⟩).lower ∧ (cell12257 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12257 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12257 ⟨36,by decide⟩).lower ∧ (cell12257 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12257 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12257 ⟨37,by decide⟩).lower ∧ (cell12257 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12257 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12257 ⟨38,by decide⟩).lower ∧ (cell12257 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12257 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12257 ⟨39,by decide⟩).lower ∧ (cell12257 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12257 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12257 ⟨40,by decide⟩).lower ∧ (cell12257 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12257 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12257 ⟨41,by decide⟩).lower ∧ (cell12257 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12257 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12257 ⟨42,by decide⟩).lower ∧ (cell12257 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12257 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12257 ⟨43,by decide⟩).lower ∧ (cell12257 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12257 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12257 ⟨44,by decide⟩).lower ∧ (cell12257 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12257 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12257 ⟨45,by decide⟩).lower ∧ (cell12257 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12257 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12257 ⟨46,by decide⟩).lower ∧ (cell12257 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12257 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12257 ⟨47,by decide⟩).lower ∧ (cell12257 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12257 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12257 ⟨48,by decide⟩).lower ∧ (cell12257 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12257 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12257 ⟨49,by decide⟩).lower ∧ (cell12257 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12257 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12257 ⟨50,by decide⟩).lower ∧ (cell12257 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12257 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12257 ⟨51,by decide⟩).lower ∧ (cell12257 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12257 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12257 ⟨52,by decide⟩).lower ∧ (cell12257 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12257 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12257 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12257 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12257,cell12257,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12257 i).lower ∧
    (cell12257 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12257 i).upper ≤ (0.532 : ℝ) ∧
    (cell12257 i).centre ≤ (0.1 : ℝ) ∧ (cell12257 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12257 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12257 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12257

/-! The local source numeric instances at 12257 have no network premises. -/
namespace BstLean.Part264b.N12257
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12257 cell12257)

noncomputable def sourceNumerics12257 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12257 (cell12257 i)
      scalarRow12257.M scalarRow12257.H scalarRow12257.xi := by
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
    energy_allowance := scalarRow12257.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12257]
    centre_nonneg := (scalarRow12257.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12257]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12257
/-! Actual 12258 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12258
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12258 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12258 12258 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12258.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12258 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12258 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12258 := gPlus_lower 12258
end BstLean.Part264b.N12258

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12258
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036454838480 : ℝ) ≤ wn 12258 := by
  have hn : √(12258 : ℝ) ≤ 110.715852523476 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12258 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.715852523476 ≤ 2 / √12258 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261125868 : ℝ) ≤ rhoBar 12258 BstLean.Part154.csC ∧
    rhoBar 12258 BstLean.Part154.csC ≤ 0.000261138910 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036454838480 : ℝ) / (1.295212 * 12258) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12258) := by gcongr
      _ ≤ (0.000261138910 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12258 BstLean.Part154.csC) ≤ 0.001044623834 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12258 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12258 BstLean.Part154.csC) (piBar (rhoBar 12258 BstLean.Part154.csC)) ≤ 0.000199460002 ∧
    cc1 (rhoBar 12258 BstLean.Part154.csC) (piBar (rhoBar 12258 BstLean.Part154.csC)) ≤ 0.000126917654 ∧
    cc2 (rhoBar 12258 BstLean.Part154.csC) ≤ 0.000073676585 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12258 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12258 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12258 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12258 BstLean.Part154.csC * nuR (rhoBar 12258 BstLean.Part154.csC)) ≤ 0.000522294869 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261138910 : ℝ) * 0.001044623834 := by gcongr
      _ ≤ (0.000522294869 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12258 BstLean.Part154.csC) * nuR (rhoBar 12258 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044623834 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12258 BstLean.Part154.csC) * rhoBar 12258 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261138910 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261138910 / 2 + 0.399 * 0.001044623834 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199460002 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522294869 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126917654 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261138910 / 1.414213562 := by gcongr
      _ ≤ (0.000073676585 : ℝ) := by norm_num

end BstLean.Part264b.N12258

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12258
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12258 BstLean.Part154.csC) (piBar (rhoBar 12258 BstLean.Part154.csC)) ≤ 1.71809E-7 := by
  have hr0 : 0 ≤ rhoBar 12258 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12258 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12258 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12258 BstLean.Part154.csC) (piBar (rhoBar 12258 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12258 BstLean.Part154.csC) (piBar (rhoBar 12258 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12258 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199460002 : ℝ) ^ 2 + 0.000126917654 ^ 2 + 3 * 0.000073676585 ^ 2 +
        2 * 0.797885 * 0.000199460002 * 0.000126917654 + 2 * 0.000199460002 * 0.000073676585 +
        4 * 0.797885 * 0.000126917654 * 0.000073676585 := by gcongr
    _ ≤ (1.71809E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12258 BstLean.Part154.csC Θ ≤ 0.002727893471 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12258 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12258 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12258 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12258 BstLean.Part154.csC) (piBar (rhoBar 12258 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12258 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71809E-7 / (0.000261125868 : ℝ) := by gcongr
    _ ≤ 0.002727893471 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12258 BstLean.Part154.csC Θ ≤ 0.003028633654 + 0.000689260187 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12258 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12258 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12258 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261138910 +
        (6863 / 10000) * 0.000261138910 * 12258 * 0.001044623834) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003028633654 + 0.000689260187 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12258 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12258 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12258 0.011 Θ ∧ gammaRatio 12258 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12258 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12258) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12258 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12258 0.011 Θ) :=
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
    badAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12258 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12258 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12258 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12258 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12258 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12258 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12258 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12258 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12258 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12258 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12258 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004128633654 + 0.003417153658 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12258

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12258
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12258 BstLean.Part154.csC) (piBar (rhoBar 12258 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12258 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12258 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12258 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12258 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12258 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12258 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12258 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12258 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12258 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12258 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12258 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12258 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053432526582 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12258) ≤ 0.010786509374 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12258 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010786509374 + 2 * 0.737676 / 12258) := by gcongr
    _ ≤ (0.053432526582 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12258 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12258

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12258
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482858990 : ℝ) ≤ plow 12258 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12258) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053429239325)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432144073) : eMP 12258 0.011 xi bn ≤ 0.001232246949 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12258 : ℝ) * (1 - 0.011))) ≤ 0.000609200655 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001432144073 / (12258 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609200655 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609200655 : ℝ) + 3.141593 * 0.053429239325 / (12258 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001232246949 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053429239325)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432144073) : PiBarMP 12258 12 0.011 xi bn ≤ 0.164166109925 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12258 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037843679433 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.105231483340 : ℝ) ≤ √((12258 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.715852523475 : ℝ) ≤ √12258 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12258) ≤ 0.125839326034 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037843679433 + 0.053429239325 * 1.772454 / (2 * (110.105231483340 : ℝ))) * (1 + 0.001232246949) +
        8 / (12258 * 110.715852523475) + 0.125839326034 := by gcongr
    _ ≤ (0.164166109925 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053429239325)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432144073) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284580183557) :
    parallelOracle 12258 0.011 xi bn cd ≤ 0.165195081530 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12258 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12258 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482858990 : ℝ) ≤ plow 12258 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.715852523475 : ℝ) ≤ √12258 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284580183557 : ℝ) / (2 * 0.560482858990 * 110.715852523475)) * 0.164166109925 +
        0.284580183557 ^ 2 / (2 * 0.560482858990 * 110.715852523475) := by gcongr
    _ ≤ (0.165195081530 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053429239325) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432144073)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284580183557) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12258 12258 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482858990 : ℝ) ≤ plow 12258 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.715852523475 : ℝ) ≤ √12258 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12258 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12258 Θ 1.22 ≤ 0.011977512432 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.715852523475 := by gcongr <;> linarith
      _ ≤ (0.011977512432 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12258 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12258 12258 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12258 12258 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12258 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12258 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12258 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12258 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165195081530 + 0.011977512432 + (0.008646 : ℝ) *
        (1 + 2 * (0.284580183557 + 0.011977512432) / (0.560482858990 * 110.715852523475))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12258]

end BstLean.Part264b.N12258

/-! The original eight local profiles supply actual 12258 moment certificates. -/
namespace BstLean.Part264b.N12258
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12258 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053429239325 ∧
    0 ≤ bN 12258 BstLean.Part154.csC (groupTheta g) ∧ bN 12258 BstLean.Part154.csC (groupTheta g) ≤ 0.001432144073 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12258 12258 0.011
      (momentAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12258 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12258 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12258 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231147656975 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12258 0.011
      (momentAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12258 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12258
/-! The actual computed-centre upper energy formula at 12258. -/
namespace BstLean.Part264b.N12258
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12258

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12258
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12258 cell12258)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086903488966
  | 2 => 0.087875237397
  | 3 => 0.088849824346
  | 4 => 0.089829711145
  | 5 => 0.090817833634
  | 6 => 0.091817667056
  | 7 => 0.092833296077
  | 8 => 0.093869489810
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12258 12258 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12258 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12258

/-! Actual upper energy certificates on all 43 source endpoints at 12258. -/
namespace BstLean.Part264b.N12258
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12258 cell12258)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12258 (gMinus 12258) (1 - (cell12258 i).lower) ≤ 1 ∧
    energyUpper 12258 (gMinus 12258) (BstLean.Part211.gPlus 12258)
      (finiteEnergy 12258 12258 0.011) (1 - (cell12258 i).lower) ≤
      (cell12258 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12258) (by norm_num)
        (q := 1 - (cell12258 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12258,cell12258]) (by norm_num [scalarRow12258,cell12258])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12258,cell12258])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12258

/-! Source-cell containment and simple scalar guards at 12258. -/
namespace BstLean.Part264b.N12258
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12258 cell12258)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12258 ⟨10,by decide⟩).lower ∧ (cell12258 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12258 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12258 ⟨11,by decide⟩).lower ∧ (cell12258 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12258 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12258 ⟨12,by decide⟩).lower ∧ (cell12258 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12258 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12258 ⟨13,by decide⟩).lower ∧ (cell12258 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12258 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12258 ⟨14,by decide⟩).lower ∧ (cell12258 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12258 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12258 ⟨15,by decide⟩).lower ∧ (cell12258 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12258 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12258 ⟨16,by decide⟩).lower ∧ (cell12258 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12258 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12258 ⟨17,by decide⟩).lower ∧ (cell12258 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12258 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12258 ⟨18,by decide⟩).lower ∧ (cell12258 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12258 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12258 ⟨19,by decide⟩).lower ∧ (cell12258 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12258 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12258 ⟨20,by decide⟩).lower ∧ (cell12258 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12258 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12258 ⟨21,by decide⟩).lower ∧ (cell12258 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12258 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12258 ⟨22,by decide⟩).lower ∧ (cell12258 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12258 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12258 ⟨23,by decide⟩).lower ∧ (cell12258 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12258 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12258 ⟨24,by decide⟩).lower ∧ (cell12258 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12258 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12258 ⟨25,by decide⟩).lower ∧ (cell12258 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12258 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12258 ⟨26,by decide⟩).lower ∧ (cell12258 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12258 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12258 ⟨27,by decide⟩).lower ∧ (cell12258 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12258 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12258 ⟨28,by decide⟩).lower ∧ (cell12258 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12258 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12258 ⟨29,by decide⟩).lower ∧ (cell12258 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12258 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12258 ⟨30,by decide⟩).lower ∧ (cell12258 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12258 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12258 ⟨31,by decide⟩).lower ∧ (cell12258 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12258 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12258 ⟨32,by decide⟩).lower ∧ (cell12258 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12258 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12258 ⟨33,by decide⟩).lower ∧ (cell12258 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12258 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12258 ⟨34,by decide⟩).lower ∧ (cell12258 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12258 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12258 ⟨35,by decide⟩).lower ∧ (cell12258 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12258 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12258 ⟨36,by decide⟩).lower ∧ (cell12258 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12258 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12258 ⟨37,by decide⟩).lower ∧ (cell12258 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12258 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12258 ⟨38,by decide⟩).lower ∧ (cell12258 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12258 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12258 ⟨39,by decide⟩).lower ∧ (cell12258 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12258 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12258 ⟨40,by decide⟩).lower ∧ (cell12258 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12258 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12258 ⟨41,by decide⟩).lower ∧ (cell12258 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12258 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12258 ⟨42,by decide⟩).lower ∧ (cell12258 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12258 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12258 ⟨43,by decide⟩).lower ∧ (cell12258 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12258 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12258 ⟨44,by decide⟩).lower ∧ (cell12258 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12258 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12258 ⟨45,by decide⟩).lower ∧ (cell12258 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12258 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12258 ⟨46,by decide⟩).lower ∧ (cell12258 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12258 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12258 ⟨47,by decide⟩).lower ∧ (cell12258 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12258 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12258 ⟨48,by decide⟩).lower ∧ (cell12258 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12258 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12258 ⟨49,by decide⟩).lower ∧ (cell12258 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12258 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12258 ⟨50,by decide⟩).lower ∧ (cell12258 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12258 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12258 ⟨51,by decide⟩).lower ∧ (cell12258 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12258 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12258 ⟨52,by decide⟩).lower ∧ (cell12258 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12258 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12258 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12258 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12258,cell12258,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12258 i).lower ∧
    (cell12258 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12258 i).upper ≤ (0.532 : ℝ) ∧
    (cell12258 i).centre ≤ (0.1 : ℝ) ∧ (cell12258 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12258 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12258 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12258

/-! The local source numeric instances at 12258 have no network premises. -/
namespace BstLean.Part264b.N12258
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12258 cell12258)

noncomputable def sourceNumerics12258 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12258 (cell12258 i)
      scalarRow12258.M scalarRow12258.H scalarRow12258.xi := by
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
    energy_allowance := scalarRow12258.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12258]
    centre_nonneg := (scalarRow12258.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12258]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12258
/-! Actual 12259 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12259
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12259 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12259 12259 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12259.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12259 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12259 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12259 := gPlus_lower 12259
end BstLean.Part264b.N12259

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12259
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036453338280 : ℝ) ≤ wn 12259 := by
  have hn : √(12259 : ℝ) ≤ 110.720368496497 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12259 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.720368496497 ≤ 2 / √12259 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261104190 : ℝ) ≤ rhoBar 12259 BstLean.Part154.csC ∧
    rhoBar 12259 BstLean.Part154.csC ≤ 0.000261117609 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036453338280 : ℝ) / (1.295212 * 12259) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12259) := by gcongr
      _ ≤ (0.000261117609 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12259 BstLean.Part154.csC) ≤ 0.001044538619 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12259 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12259 BstLean.Part154.csC) (piBar (rhoBar 12259 BstLean.Part154.csC)) ≤ 0.000199443732 ∧
    cc1 (rhoBar 12259 BstLean.Part154.csC) (piBar (rhoBar 12259 BstLean.Part154.csC)) ≤ 0.000126907301 ∧
    cc2 (rhoBar 12259 BstLean.Part154.csC) ≤ 0.000073670575 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12259 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12259 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12259 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12259 BstLean.Part154.csC * nuR (rhoBar 12259 BstLean.Part154.csC)) ≤ 0.000522252264 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261117609 : ℝ) * 0.001044538619 := by gcongr
      _ ≤ (0.000522252264 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12259 BstLean.Part154.csC) * nuR (rhoBar 12259 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044538619 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12259 BstLean.Part154.csC) * rhoBar 12259 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261117609 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261117609 / 2 + 0.399 * 0.001044538619 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199443732 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522252264 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126907301 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261117609 / 1.414213562 := by gcongr
      _ ≤ (0.000073670575 : ℝ) := by norm_num

end BstLean.Part264b.N12259

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12259
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12259 BstLean.Part154.csC) (piBar (rhoBar 12259 BstLean.Part154.csC)) ≤ 1.71781E-7 := by
  have hr0 : 0 ≤ rhoBar 12259 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12259 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12259 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12259 BstLean.Part154.csC) (piBar (rhoBar 12259 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12259 BstLean.Part154.csC) (piBar (rhoBar 12259 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12259 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199443732 : ℝ) ^ 2 + 0.000126907301 ^ 2 + 3 * 0.000073670575 ^ 2 +
        2 * 0.797885 * 0.000199443732 * 0.000126907301 + 2 * 0.000199443732 * 0.000073670575 +
        4 * 0.797885 * 0.000126907301 * 0.000073670575 := by gcongr
    _ ≤ (1.71781E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12259 BstLean.Part154.csC Θ ≤ 0.002727675346 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12259 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12259 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12259 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12259 BstLean.Part154.csC) (piBar (rhoBar 12259 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12259 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71781E-7 / (0.000261104190 : ℝ) := by gcongr
    _ ≤ 0.002727675346 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12259 BstLean.Part154.csC Θ ≤ 0.003028386603 + 0.000689203964 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12259 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12259 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12259 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261117609 +
        (6863 / 10000) * 0.000261117609 * 12259 * 0.001044538619) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003028386603 + 0.000689203964 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12259 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12259 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12259 0.011 Θ ∧ gammaRatio 12259 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12259 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12259) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12259 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12259 0.011 Θ) :=
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
    badAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12259 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12259 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12259 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12259 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12259 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12259 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12259 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12259 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12259 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12259 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12259 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004128386603 + 0.003416879310 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12259

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12259
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12259 BstLean.Part154.csC) (piBar (rhoBar 12259 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12259 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12259 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12259 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12259 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12259 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12259 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12259 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12259 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12259 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12259 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12259 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12259 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053430323172 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12259) ≤ 0.010786069423 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12259 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010786069423 + 2 * 0.737676 / 12259) := by gcongr
    _ ≤ (0.053430323172 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12259 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12259

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12259
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482907529 : ℝ) ≤ plow 12259 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12259) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428848241)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432029557) : eMP 12259 0.011 xi bn ≤ 0.001232147311 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12259 : ℝ) * (1 - 0.011))) ≤ 0.000609151451 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001432029557 / (12259 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609151451 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609151451 : ℝ) + 3.141593 * 0.053428848241 / (12259 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001232147311 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428848241)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432029557) : PiBarMP 12259 12 0.011 xi bn ≤ 0.164159437136 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12259 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037842166389 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.109722549827 : ℝ) ≤ √((12259 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.720368496496 : ℝ) ≤ √12259 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12259) ≤ 0.125834193401 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037842166389 + 0.053428848241 * 1.772454 / (2 * (110.109722549827 : ℝ))) * (1 + 0.001232147311) +
        8 / (12259 * 110.720368496496) + 0.125834193401 := by gcongr
    _ ≤ (0.164159437136 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428848241)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432029557) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284577134184) :
    parallelOracle 12259 0.011 xi bn cd ≤ 0.165188333366 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12259 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12259 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482907529 : ℝ) ≤ plow 12259 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.720368496496 : ℝ) ≤ √12259 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284577134184 : ℝ) / (2 * 0.560482907529 * 110.720368496496)) * 0.164159437136 +
        0.284577134184 ^ 2 / (2 * 0.560482907529 * 110.720368496496) := by gcongr
    _ ≤ (0.165188333366 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428848241) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001432029557)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284577134184) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12259 12259 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482907529 : ℝ) ≤ plow 12259 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.720368496496 : ℝ) ≤ √12259 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12259 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12259 Θ 1.22 ≤ 0.011977023903 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.720368496496 := by gcongr <;> linarith
      _ ≤ (0.011977023903 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12259 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12259 12259 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12259 12259 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12259 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12259 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12259 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12259 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165188333366 + 0.011977023903 + (0.008646 : ℝ) *
        (1 + 2 * (0.284577134184 + 0.011977023903) / (0.560482907529 * 110.720368496496))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12259]

end BstLean.Part264b.N12259

/-! The original eight local profiles supply actual 12259 moment certificates. -/
namespace BstLean.Part264b.N12259
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12259 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053428848241 ∧
    0 ≤ bN 12259 BstLean.Part154.csC (groupTheta g) ∧ bN 12259 BstLean.Part154.csC (groupTheta g) ≤ 0.001432029557 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12259 12259 0.011
      (momentAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12259 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12259 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12259 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231146811012 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12259 0.011
      (momentAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12259 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12259
/-! The actual computed-centre upper energy formula at 12259. -/
namespace BstLean.Part264b.N12259
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12259

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12259
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12259 cell12259)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086899963396
  | 2 => 0.087871631670
  | 3 => 0.088846124445
  | 4 => 0.089825900034
  | 5 => 0.090813890762
  | 6 => 0.091813567803
  | 7 => 0.092829011148
  | 8 => 0.093864984563
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12259 12259 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12259 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12259

/-! Actual upper energy certificates on all 43 source endpoints at 12259. -/
namespace BstLean.Part264b.N12259
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12259 cell12259)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12259 (gMinus 12259) (1 - (cell12259 i).lower) ≤ 1 ∧
    energyUpper 12259 (gMinus 12259) (BstLean.Part211.gPlus 12259)
      (finiteEnergy 12259 12259 0.011) (1 - (cell12259 i).lower) ≤
      (cell12259 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12259) (by norm_num)
        (q := 1 - (cell12259 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12259,cell12259]) (by norm_num [scalarRow12259,cell12259])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12259,cell12259])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12259

/-! Source-cell containment and simple scalar guards at 12259. -/
namespace BstLean.Part264b.N12259
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12259 cell12259)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12259 ⟨10,by decide⟩).lower ∧ (cell12259 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12259 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12259 ⟨11,by decide⟩).lower ∧ (cell12259 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12259 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12259 ⟨12,by decide⟩).lower ∧ (cell12259 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12259 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12259 ⟨13,by decide⟩).lower ∧ (cell12259 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12259 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12259 ⟨14,by decide⟩).lower ∧ (cell12259 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12259 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12259 ⟨15,by decide⟩).lower ∧ (cell12259 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12259 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12259 ⟨16,by decide⟩).lower ∧ (cell12259 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12259 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12259 ⟨17,by decide⟩).lower ∧ (cell12259 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12259 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12259 ⟨18,by decide⟩).lower ∧ (cell12259 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12259 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12259 ⟨19,by decide⟩).lower ∧ (cell12259 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12259 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12259 ⟨20,by decide⟩).lower ∧ (cell12259 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12259 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12259 ⟨21,by decide⟩).lower ∧ (cell12259 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12259 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12259 ⟨22,by decide⟩).lower ∧ (cell12259 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12259 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12259 ⟨23,by decide⟩).lower ∧ (cell12259 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12259 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12259 ⟨24,by decide⟩).lower ∧ (cell12259 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12259 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12259 ⟨25,by decide⟩).lower ∧ (cell12259 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12259 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12259 ⟨26,by decide⟩).lower ∧ (cell12259 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12259 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12259 ⟨27,by decide⟩).lower ∧ (cell12259 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12259 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12259 ⟨28,by decide⟩).lower ∧ (cell12259 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12259 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12259 ⟨29,by decide⟩).lower ∧ (cell12259 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12259 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12259 ⟨30,by decide⟩).lower ∧ (cell12259 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12259 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12259 ⟨31,by decide⟩).lower ∧ (cell12259 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12259 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12259 ⟨32,by decide⟩).lower ∧ (cell12259 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12259 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12259 ⟨33,by decide⟩).lower ∧ (cell12259 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12259 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12259 ⟨34,by decide⟩).lower ∧ (cell12259 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12259 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12259 ⟨35,by decide⟩).lower ∧ (cell12259 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12259 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12259 ⟨36,by decide⟩).lower ∧ (cell12259 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12259 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12259 ⟨37,by decide⟩).lower ∧ (cell12259 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12259 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12259 ⟨38,by decide⟩).lower ∧ (cell12259 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12259 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12259 ⟨39,by decide⟩).lower ∧ (cell12259 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12259 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12259 ⟨40,by decide⟩).lower ∧ (cell12259 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12259 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12259 ⟨41,by decide⟩).lower ∧ (cell12259 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12259 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12259 ⟨42,by decide⟩).lower ∧ (cell12259 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12259 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12259 ⟨43,by decide⟩).lower ∧ (cell12259 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12259 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12259 ⟨44,by decide⟩).lower ∧ (cell12259 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12259 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12259 ⟨45,by decide⟩).lower ∧ (cell12259 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12259 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12259 ⟨46,by decide⟩).lower ∧ (cell12259 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12259 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12259 ⟨47,by decide⟩).lower ∧ (cell12259 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12259 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12259 ⟨48,by decide⟩).lower ∧ (cell12259 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12259 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12259 ⟨49,by decide⟩).lower ∧ (cell12259 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12259 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12259 ⟨50,by decide⟩).lower ∧ (cell12259 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12259 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12259 ⟨51,by decide⟩).lower ∧ (cell12259 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12259 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12259 ⟨52,by decide⟩).lower ∧ (cell12259 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12259 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12259 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12259 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12259,cell12259,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12259 i).lower ∧
    (cell12259 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12259 i).upper ≤ (0.532 : ℝ) ∧
    (cell12259 i).centre ≤ (0.1 : ℝ) ∧ (cell12259 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12259 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12259 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12259

/-! The local source numeric instances at 12259 have no network premises. -/
namespace BstLean.Part264b.N12259
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12259 cell12259)

noncomputable def sourceNumerics12259 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12259 (cell12259 i)
      scalarRow12259.M scalarRow12259.H scalarRow12259.xi := by
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
    energy_allowance := scalarRow12259.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12259]
    centre_nonneg := (scalarRow12259.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12259]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12259
/-! Actual 12260 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12260
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12260 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12260 12260 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12260.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12260 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12260 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12260 := gPlus_lower 12260
end BstLean.Part264b.N12260

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12260
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036451838266 : ℝ) ≤ wn 12260 := by
  have hn : √(12260 : ℝ) ≤ 110.724884285332 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12260 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.724884285332 ≤ 2 / √12260 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261082515 : ℝ) ≤ rhoBar 12260 BstLean.Part154.csC ∧
    rhoBar 12260 BstLean.Part154.csC ≤ 0.000261096310 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036451838266 : ℝ) / (1.295212 * 12260) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12260) := by gcongr
      _ ≤ (0.000261096310 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12260 BstLean.Part154.csC) ≤ 0.001044453412 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12260 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12260 BstLean.Part154.csC) (piBar (rhoBar 12260 BstLean.Part154.csC)) ≤ 0.000199427462 ∧
    cc1 (rhoBar 12260 BstLean.Part154.csC) (piBar (rhoBar 12260 BstLean.Part154.csC)) ≤ 0.000126896949 ∧
    cc2 (rhoBar 12260 BstLean.Part154.csC) ≤ 0.000073664566 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12260 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12260 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12260 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12260 BstLean.Part154.csC * nuR (rhoBar 12260 BstLean.Part154.csC)) ≤ 0.000522209663 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261096310 : ℝ) * 0.001044453412 := by gcongr
      _ ≤ (0.000522209663 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12260 BstLean.Part154.csC) * nuR (rhoBar 12260 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044453412 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12260 BstLean.Part154.csC) * rhoBar 12260 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261096310 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261096310 / 2 + 0.399 * 0.001044453412 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199427462 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522209663 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126896949 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261096310 / 1.414213562 := by gcongr
      _ ≤ (0.000073664566 : ℝ) := by norm_num

end BstLean.Part264b.N12260

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12260
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12260 BstLean.Part154.csC) (piBar (rhoBar 12260 BstLean.Part154.csC)) ≤ 1.71753E-7 := by
  have hr0 : 0 ≤ rhoBar 12260 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12260 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12260 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12260 BstLean.Part154.csC) (piBar (rhoBar 12260 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12260 BstLean.Part154.csC) (piBar (rhoBar 12260 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12260 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199427462 : ℝ) ^ 2 + 0.000126896949 ^ 2 + 3 * 0.000073664566 ^ 2 +
        2 * 0.797885 * 0.000199427462 * 0.000126896949 + 2 * 0.000199427462 * 0.000073664566 +
        4 * 0.797885 * 0.000126896949 * 0.000073664566 := by gcongr
    _ ≤ (1.71753E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12260 BstLean.Part154.csC Θ ≤ 0.002727457154 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12260 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12260 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12260 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12260 BstLean.Part154.csC) (piBar (rhoBar 12260 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12260 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71753E-7 / (0.000261082515 : ℝ) := by gcongr
    _ ≤ 0.002727457154 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12260 BstLean.Part154.csC Θ ≤ 0.003028139558 + 0.000689147747 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12260 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12260 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12260 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261096310 +
        (6863 / 10000) * 0.000261096310 * 12260 * 0.001044453412) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003028139558 + 0.000689147747 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12260 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12260 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12260 0.011 Θ ∧ gammaRatio 12260 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12260 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12260) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12260 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12260 0.011 Θ) :=
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
    badAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12260 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12260 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12260 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12260 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12260 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12260 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12260 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12260 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12260 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12260 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12260 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004128139558 + 0.003416604901 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12260

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12260
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12260 BstLean.Part154.csC) (piBar (rhoBar 12260 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12260 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12260 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12260 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12260 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12260 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12260 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12260 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12260 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12260 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12260 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12260 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12260 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053428120031 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12260) ≤ 0.010785629525 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12260 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010785629525 + 2 * 0.737676 / 12260) := by gcongr
    _ ≤ (0.053428120031 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12260 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12260

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12260
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560482956060 : ℝ) ≤ plow 12260 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12260) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428457132)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431915006) : eMP 12260 0.011 xi bn ≤ 0.001232047668 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12260 : ℝ) * (1 - 0.011))) ≤ 0.000609102245 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001431915006 / (12260 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609102245 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609102245 : ℝ) + 3.141593 * 0.053428457132 / (12260 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001232047668 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428457132)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431915006) : PiBarMP 12260 12 0.011 xi bn ≤ 0.164152764454 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12260 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037840652823 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.114213433144 : ℝ) ≤ √((12260 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.724884285331 : ℝ) ≤ √12260 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12260) ≤ 0.125829061396 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037840652823 + 0.053428457132 * 1.772454 / (2 * (110.114213433144 : ℝ))) * (1 + 0.001232047668) +
        8 / (12260 * 110.724884285331) + 0.125829061396 := by gcongr
    _ ≤ (0.164152764454 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428457132)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431915006) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284574085023) :
    parallelOracle 12260 0.011 xi bn cd ≤ 0.165181585319 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12260 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12260 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560482956060 : ℝ) ≤ plow 12260 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.724884285331 : ℝ) ≤ √12260 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284574085023 : ℝ) / (2 * 0.560482956060 * 110.724884285331)) * 0.164152764454 +
        0.284574085023 ^ 2 / (2 * 0.560482956060 * 110.724884285331) := by gcongr
    _ ≤ (0.165181585319 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428457132) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431915006)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284574085023) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12260 12260 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560482956060 : ℝ) ≤ plow 12260 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.724884285331 : ℝ) ≤ √12260 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12260 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12260 Θ 1.22 ≤ 0.011976535434 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.724884285331 := by gcongr <;> linarith
      _ ≤ (0.011976535434 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12260 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12260 12260 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12260 12260 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12260 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12260 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12260 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12260 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165181585319 + 0.011976535434 + (0.008646 : ℝ) *
        (1 + 2 * (0.284574085023 + 0.011976535434) / (0.560482956060 * 110.724884285331))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12260]

end BstLean.Part264b.N12260

/-! The original eight local profiles supply actual 12260 moment certificates. -/
namespace BstLean.Part264b.N12260
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12260 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053428457132 ∧
    0 ≤ bN 12260 BstLean.Part154.csC (groupTheta g) ∧ bN 12260 BstLean.Part154.csC (groupTheta g) ≤ 0.001431915006 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12260 12260 0.011
      (momentAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12260 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12260 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12260 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231145964992 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12260 0.011
      (momentAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12260 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12260
/-! The actual computed-centre upper energy formula at 12260. -/
namespace BstLean.Part264b.N12260
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12260

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12260
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12260 cell12260)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086896439563
  | 2 => 0.087868027758
  | 3 => 0.088842426458
  | 4 => 0.089822090958
  | 5 => 0.090809950070
  | 6 => 0.091809470906
  | 7 => 0.092824728784
  | 8 => 0.093860482135
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12260 12260 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12260 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12260

/-! Actual upper energy certificates on all 43 source endpoints at 12260. -/
namespace BstLean.Part264b.N12260
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12260 cell12260)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12260 (gMinus 12260) (1 - (cell12260 i).lower) ≤ 1 ∧
    energyUpper 12260 (gMinus 12260) (BstLean.Part211.gPlus 12260)
      (finiteEnergy 12260 12260 0.011) (1 - (cell12260 i).lower) ≤
      (cell12260 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12260) (by norm_num)
        (q := 1 - (cell12260 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12260,cell12260]) (by norm_num [scalarRow12260,cell12260])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12260,cell12260])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12260

/-! Source-cell containment and simple scalar guards at 12260. -/
namespace BstLean.Part264b.N12260
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12260 cell12260)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12260 ⟨10,by decide⟩).lower ∧ (cell12260 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12260 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12260 ⟨11,by decide⟩).lower ∧ (cell12260 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12260 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12260 ⟨12,by decide⟩).lower ∧ (cell12260 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12260 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12260 ⟨13,by decide⟩).lower ∧ (cell12260 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12260 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12260 ⟨14,by decide⟩).lower ∧ (cell12260 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12260 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12260 ⟨15,by decide⟩).lower ∧ (cell12260 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12260 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12260 ⟨16,by decide⟩).lower ∧ (cell12260 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12260 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12260 ⟨17,by decide⟩).lower ∧ (cell12260 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12260 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12260 ⟨18,by decide⟩).lower ∧ (cell12260 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12260 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12260 ⟨19,by decide⟩).lower ∧ (cell12260 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12260 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12260 ⟨20,by decide⟩).lower ∧ (cell12260 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12260 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12260 ⟨21,by decide⟩).lower ∧ (cell12260 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12260 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12260 ⟨22,by decide⟩).lower ∧ (cell12260 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12260 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12260 ⟨23,by decide⟩).lower ∧ (cell12260 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12260 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12260 ⟨24,by decide⟩).lower ∧ (cell12260 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12260 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12260 ⟨25,by decide⟩).lower ∧ (cell12260 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12260 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12260 ⟨26,by decide⟩).lower ∧ (cell12260 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12260 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12260 ⟨27,by decide⟩).lower ∧ (cell12260 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12260 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12260 ⟨28,by decide⟩).lower ∧ (cell12260 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12260 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12260 ⟨29,by decide⟩).lower ∧ (cell12260 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12260 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12260 ⟨30,by decide⟩).lower ∧ (cell12260 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12260 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12260 ⟨31,by decide⟩).lower ∧ (cell12260 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12260 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12260 ⟨32,by decide⟩).lower ∧ (cell12260 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12260 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12260 ⟨33,by decide⟩).lower ∧ (cell12260 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12260 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12260 ⟨34,by decide⟩).lower ∧ (cell12260 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12260 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12260 ⟨35,by decide⟩).lower ∧ (cell12260 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12260 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12260 ⟨36,by decide⟩).lower ∧ (cell12260 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12260 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12260 ⟨37,by decide⟩).lower ∧ (cell12260 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12260 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12260 ⟨38,by decide⟩).lower ∧ (cell12260 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12260 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12260 ⟨39,by decide⟩).lower ∧ (cell12260 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12260 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12260 ⟨40,by decide⟩).lower ∧ (cell12260 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12260 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12260 ⟨41,by decide⟩).lower ∧ (cell12260 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12260 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12260 ⟨42,by decide⟩).lower ∧ (cell12260 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12260 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12260 ⟨43,by decide⟩).lower ∧ (cell12260 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12260 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12260 ⟨44,by decide⟩).lower ∧ (cell12260 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12260 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12260 ⟨45,by decide⟩).lower ∧ (cell12260 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12260 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12260 ⟨46,by decide⟩).lower ∧ (cell12260 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12260 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12260 ⟨47,by decide⟩).lower ∧ (cell12260 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12260 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12260 ⟨48,by decide⟩).lower ∧ (cell12260 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12260 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12260 ⟨49,by decide⟩).lower ∧ (cell12260 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12260 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12260 ⟨50,by decide⟩).lower ∧ (cell12260 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12260 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12260 ⟨51,by decide⟩).lower ∧ (cell12260 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12260 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12260 ⟨52,by decide⟩).lower ∧ (cell12260 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12260 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12260 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12260 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12260,cell12260,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12260 i).lower ∧
    (cell12260 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12260 i).upper ≤ (0.532 : ℝ) ∧
    (cell12260 i).centre ≤ (0.1 : ℝ) ∧ (cell12260 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12260 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12260 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12260

/-! The local source numeric instances at 12260 have no network premises. -/
namespace BstLean.Part264b.N12260
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12260 cell12260)

noncomputable def sourceNumerics12260 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12260 (cell12260 i)
      scalarRow12260.M scalarRow12260.H scalarRow12260.xi := by
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
    energy_allowance := scalarRow12260.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12260]
    centre_nonneg := (scalarRow12260.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12260]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12260
/-! Actual 12261 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12261
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12261 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12261 12261 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12261.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12261 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12261 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12261 := gPlus_lower 12261
end BstLean.Part264b.N12261

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12261
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036450338435 : ℝ) ≤ wn 12261 := by
  have hn : √(12261 : ℝ) ≤ 110.729399890003 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12261 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.729399890003 ≤ 2 / √12261 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261060843 : ℝ) ≤ rhoBar 12261 BstLean.Part154.csC ∧
    rhoBar 12261 BstLean.Part154.csC ≤ 0.000261075015 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036450338435 : ℝ) / (1.295212 * 12261) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12261) := by gcongr
      _ ≤ (0.000261075015 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12261 BstLean.Part154.csC) ≤ 0.001044368221 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12261 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12261 BstLean.Part154.csC) (piBar (rhoBar 12261 BstLean.Part154.csC)) ≤ 0.000199411196 ∧
    cc1 (rhoBar 12261 BstLean.Part154.csC) (piBar (rhoBar 12261 BstLean.Part154.csC)) ≤ 0.000126886599 ∧
    cc2 (rhoBar 12261 BstLean.Part154.csC) ≤ 0.000073658558 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12261 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12261 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12261 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12261 BstLean.Part154.csC * nuR (rhoBar 12261 BstLean.Part154.csC)) ≤ 0.000522167070 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261075015 : ℝ) * 0.001044368221 := by gcongr
      _ ≤ (0.000522167070 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12261 BstLean.Part154.csC) * nuR (rhoBar 12261 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044368221 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12261 BstLean.Part154.csC) * rhoBar 12261 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261075015 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261075015 / 2 + 0.399 * 0.001044368221 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199411196 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522167070 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126886599 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261075015 / 1.414213562 := by gcongr
      _ ≤ (0.000073658558 : ℝ) := by norm_num

end BstLean.Part264b.N12261

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12261
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12261 BstLean.Part154.csC) (piBar (rhoBar 12261 BstLean.Part154.csC)) ≤ 1.71725E-7 := by
  have hr0 : 0 ≤ rhoBar 12261 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12261 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12261 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12261 BstLean.Part154.csC) (piBar (rhoBar 12261 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12261 BstLean.Part154.csC) (piBar (rhoBar 12261 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12261 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199411196 : ℝ) ^ 2 + 0.000126886599 ^ 2 + 3 * 0.000073658558 ^ 2 +
        2 * 0.797885 * 0.000199411196 * 0.000126886599 + 2 * 0.000199411196 * 0.000073658558 +
        4 * 0.797885 * 0.000126886599 * 0.000073658558 := by gcongr
    _ ≤ (1.71725E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12261 BstLean.Part154.csC Θ ≤ 0.002727238894 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12261 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12261 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12261 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12261 BstLean.Part154.csC) (piBar (rhoBar 12261 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12261 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71725E-7 / (0.000261060843 : ℝ) := by gcongr
    _ ≤ 0.002727238894 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12261 BstLean.Part154.csC Θ ≤ 0.003027892566 + 0.000689091540 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12261 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12261 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12261 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261075015 +
        (6863 / 10000) * 0.000261075015 * 12261 * 0.001044368221) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003027892566 + 0.000689091540 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12261 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12261 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12261 0.011 Θ ∧ gammaRatio 12261 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12261 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12261) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12261 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12261 0.011 Θ) :=
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
    badAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12261 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12261 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12261 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12261 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12261 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12261 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12261 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12261 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12261 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12261 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12261 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004127892566 + 0.003416330434 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12261

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12261
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12261 BstLean.Part154.csC) (piBar (rhoBar 12261 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12261 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12261 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12261 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12261 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12261 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12261 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12261 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12261 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12261 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12261 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12261 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12261 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053425917162 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12261) ≤ 0.010785189681 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12261 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010785189681 + 2 * 0.737676 / 12261) := by gcongr
    _ ≤ (0.053425917162 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12261 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12261

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12261
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483004583 : ℝ) ≤ plow 12261 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12261) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428066044)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431800420) : eMP 12261 0.011 xi bn ≤ 0.001231948018 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12261 : ℝ) * (1 - 0.011))) ≤ 0.000609053035 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001431800420 / (12261 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609053035 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609053035 : ℝ) + 3.141593 * 0.053428066044 / (12261 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001231948018 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428066044)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431800420) : PiBarMP 12261 12 0.011 xi bn ≤ 0.164146091878 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12261 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037839138733 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.118704133312 : ℝ) ≤ √((12261 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.729399890002 : ℝ) ≤ √12261 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12261) ≤ 0.125823930019 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037839138733 + 0.053428066044 * 1.772454 / (2 * (110.118704133312 : ℝ))) * (1 + 0.001231948018) +
        8 / (12261 * 110.729399890002) + 0.125823930019 := by gcongr
    _ ≤ (0.164146091878 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428066044)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431800420) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284571036177) :
    parallelOracle 12261 0.011 xi bn cd ≤ 0.165174837388 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12261 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12261 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483004583 : ℝ) ≤ plow 12261 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.729399890002 : ℝ) ≤ √12261 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284571036177 : ℝ) / (2 * 0.560483004583 * 110.729399890002)) * 0.164146091878 +
        0.284571036177 ^ 2 / (2 * 0.560483004583 * 110.729399890002) := by gcongr
    _ ≤ (0.165174837388 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053428066044) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431800420)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284571036177) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12261 12261 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483004583 : ℝ) ≤ plow 12261 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.729399890002 : ℝ) ≤ √12261 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12261 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12261 Θ 1.22 ≤ 0.011976047024 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.729399890002 := by gcongr <;> linarith
      _ ≤ (0.011976047024 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12261 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12261 12261 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12261 12261 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12261 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12261 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12261 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12261 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165174837388 + 0.011976047024 + (0.008646 : ℝ) *
        (1 + 2 * (0.284571036177 + 0.011976047024) / (0.560483004583 * 110.729399890002))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12261]

end BstLean.Part264b.N12261

/-! The original eight local profiles supply actual 12261 moment certificates. -/
namespace BstLean.Part264b.N12261
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12261 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053428066044 ∧
    0 ≤ bN 12261 BstLean.Part154.csC (groupTheta g) ∧ bN 12261 BstLean.Part154.csC (groupTheta g) ≤ 0.001431800420 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12261 12261 0.011
      (momentAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12261 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12261 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12261 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231145119015 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12261 0.011
      (momentAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12261 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12261
/-! The actual computed-centre upper energy formula at 12261. -/
namespace BstLean.Part264b.N12261
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12261

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12261
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12261 cell12261)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086892917466
  | 2 => 0.087864425662
  | 3 => 0.088838730383
  | 4 => 0.089818283912
  | 5 => 0.090806011554
  | 6 => 0.091805376360
  | 7 => 0.092820448983
  | 8 => 0.093855982522
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12261 12261 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12261 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12261

/-! Actual upper energy certificates on all 43 source endpoints at 12261. -/
namespace BstLean.Part264b.N12261
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12261 cell12261)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12261 (gMinus 12261) (1 - (cell12261 i).lower) ≤ 1 ∧
    energyUpper 12261 (gMinus 12261) (BstLean.Part211.gPlus 12261)
      (finiteEnergy 12261 12261 0.011) (1 - (cell12261 i).lower) ≤
      (cell12261 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12261) (by norm_num)
        (q := 1 - (cell12261 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12261,cell12261]) (by norm_num [scalarRow12261,cell12261])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12261,cell12261])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12261

/-! Source-cell containment and simple scalar guards at 12261. -/
namespace BstLean.Part264b.N12261
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12261 cell12261)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12261 ⟨10,by decide⟩).lower ∧ (cell12261 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12261 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12261 ⟨11,by decide⟩).lower ∧ (cell12261 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12261 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12261 ⟨12,by decide⟩).lower ∧ (cell12261 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12261 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12261 ⟨13,by decide⟩).lower ∧ (cell12261 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12261 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12261 ⟨14,by decide⟩).lower ∧ (cell12261 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12261 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12261 ⟨15,by decide⟩).lower ∧ (cell12261 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12261 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12261 ⟨16,by decide⟩).lower ∧ (cell12261 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12261 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12261 ⟨17,by decide⟩).lower ∧ (cell12261 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12261 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12261 ⟨18,by decide⟩).lower ∧ (cell12261 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12261 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12261 ⟨19,by decide⟩).lower ∧ (cell12261 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12261 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12261 ⟨20,by decide⟩).lower ∧ (cell12261 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12261 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12261 ⟨21,by decide⟩).lower ∧ (cell12261 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12261 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12261 ⟨22,by decide⟩).lower ∧ (cell12261 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12261 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12261 ⟨23,by decide⟩).lower ∧ (cell12261 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12261 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12261 ⟨24,by decide⟩).lower ∧ (cell12261 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12261 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12261 ⟨25,by decide⟩).lower ∧ (cell12261 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12261 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12261 ⟨26,by decide⟩).lower ∧ (cell12261 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12261 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12261 ⟨27,by decide⟩).lower ∧ (cell12261 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12261 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12261 ⟨28,by decide⟩).lower ∧ (cell12261 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12261 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12261 ⟨29,by decide⟩).lower ∧ (cell12261 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12261 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12261 ⟨30,by decide⟩).lower ∧ (cell12261 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12261 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12261 ⟨31,by decide⟩).lower ∧ (cell12261 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12261 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12261 ⟨32,by decide⟩).lower ∧ (cell12261 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12261 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12261 ⟨33,by decide⟩).lower ∧ (cell12261 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12261 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12261 ⟨34,by decide⟩).lower ∧ (cell12261 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12261 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12261 ⟨35,by decide⟩).lower ∧ (cell12261 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12261 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12261 ⟨36,by decide⟩).lower ∧ (cell12261 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12261 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12261 ⟨37,by decide⟩).lower ∧ (cell12261 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12261 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12261 ⟨38,by decide⟩).lower ∧ (cell12261 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12261 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12261 ⟨39,by decide⟩).lower ∧ (cell12261 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12261 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12261 ⟨40,by decide⟩).lower ∧ (cell12261 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12261 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12261 ⟨41,by decide⟩).lower ∧ (cell12261 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12261 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12261 ⟨42,by decide⟩).lower ∧ (cell12261 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12261 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12261 ⟨43,by decide⟩).lower ∧ (cell12261 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12261 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12261 ⟨44,by decide⟩).lower ∧ (cell12261 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12261 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12261 ⟨45,by decide⟩).lower ∧ (cell12261 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12261 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12261 ⟨46,by decide⟩).lower ∧ (cell12261 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12261 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12261 ⟨47,by decide⟩).lower ∧ (cell12261 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12261 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12261 ⟨48,by decide⟩).lower ∧ (cell12261 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12261 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12261 ⟨49,by decide⟩).lower ∧ (cell12261 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12261 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12261 ⟨50,by decide⟩).lower ∧ (cell12261 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12261 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12261 ⟨51,by decide⟩).lower ∧ (cell12261 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12261 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12261 ⟨52,by decide⟩).lower ∧ (cell12261 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12261 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12261 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12261 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12261,cell12261,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12261 i).lower ∧
    (cell12261 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12261 i).upper ≤ (0.532 : ℝ) ∧
    (cell12261 i).centre ≤ (0.1 : ℝ) ∧ (cell12261 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12261 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12261 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12261

/-! The local source numeric instances at 12261 have no network premises. -/
namespace BstLean.Part264b.N12261
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12261 cell12261)

noncomputable def sourceNumerics12261 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12261 (cell12261 i)
      scalarRow12261.M scalarRow12261.H scalarRow12261.xi := by
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
    energy_allowance := scalarRow12261.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12261]
    centre_nonneg := (scalarRow12261.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12261]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12261
/-! Actual 12262 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12262
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12262 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12262 12262 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12262.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12262 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12262 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12262 := gPlus_lower 12262
end BstLean.Part264b.N12262

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12262
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036448838789 : ℝ) ≤ wn 12262 := by
  have hn : √(12262 : ℝ) ≤ 110.733915310532 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12262 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.733915310532 ≤ 2 / √12262 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261039175 : ℝ) ≤ rhoBar 12262 BstLean.Part154.csC ∧
    rhoBar 12262 BstLean.Part154.csC ≤ 0.000261053724 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036448838789 : ℝ) / (1.295212 * 12262) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12262) := by gcongr
      _ ≤ (0.000261053724 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12262 BstLean.Part154.csC) ≤ 0.001044283046 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12262 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12262 BstLean.Part154.csC) (piBar (rhoBar 12262 BstLean.Part154.csC)) ≤ 0.000199394933 ∧
    cc1 (rhoBar 12262 BstLean.Part154.csC) (piBar (rhoBar 12262 BstLean.Part154.csC)) ≤ 0.000126876251 ∧
    cc2 (rhoBar 12262 BstLean.Part154.csC) ≤ 0.000073652551 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12262 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12262 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12262 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12262 BstLean.Part154.csC * nuR (rhoBar 12262 BstLean.Part154.csC)) ≤ 0.000522124486 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261053724 : ℝ) * 0.001044283046 := by gcongr
      _ ≤ (0.000522124486 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12262 BstLean.Part154.csC) * nuR (rhoBar 12262 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001044283046 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12262 BstLean.Part154.csC) * rhoBar 12262 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261053724 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261053724 / 2 + 0.399 * 0.001044283046 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000199394933 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000522124486 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126876251 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261053724 / 1.414213562 := by gcongr
      _ ≤ (0.000073652551 : ℝ) := by norm_num

end BstLean.Part264b.N12262

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12262
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12262 BstLean.Part154.csC) (piBar (rhoBar 12262 BstLean.Part154.csC)) ≤ 1.71697E-7 := by
  have hr0 : 0 ≤ rhoBar 12262 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12262 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12262 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12262 BstLean.Part154.csC) (piBar (rhoBar 12262 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12262 BstLean.Part154.csC) (piBar (rhoBar 12262 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12262 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000199394933 : ℝ) ^ 2 + 0.000126876251 ^ 2 + 3 * 0.000073652551 ^ 2 +
        2 * 0.797885 * 0.000199394933 * 0.000126876251 + 2 * 0.000199394933 * 0.000073652551 +
        4 * 0.797885 * 0.000126876251 * 0.000073652551 := by gcongr
    _ ≤ (1.71697E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12262 BstLean.Part154.csC Θ ≤ 0.002727020556 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12262 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12262 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12262 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12262 BstLean.Part154.csC) (piBar (rhoBar 12262 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12262 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.71697E-7 / (0.000261039175 : ℝ) := by gcongr
    _ ≤ 0.002727020556 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12262 BstLean.Part154.csC Θ ≤ 0.003027645626 + 0.000689035344 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12262 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12262 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12262 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000261053724 +
        (6863 / 10000) * 0.000261053724 * 12262 * 0.001044283046) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003027645626 + 0.000689035344 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12262 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12262 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12262 0.011 Θ ∧ gammaRatio 12262 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12262 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12262) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12262 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12262 0.011 Θ) :=
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
    badAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12262 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12262 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12262 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12262 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12262 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12262 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12262 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12262 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12262 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12262 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12262 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004127645626 + 0.003416055900 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12262

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12262
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12262 BstLean.Part154.csC) (piBar (rhoBar 12262 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12262 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12262 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12262 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12262 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12262 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12262 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12262 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12262 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12262 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12262 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12262 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12262 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053423714565 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12262) ≤ 0.010784749891 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12262 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010784749891 + 2 * 0.737676 / 12262) := by gcongr
    _ ≤ (0.053423714565 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12262 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12262

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12262
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560483053099 : ℝ) ≤ plow 12262 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12262) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053427674974)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431685792) : eMP 12262 0.011 xi bn ≤ 0.001231848358 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12262 : ℝ) * (1 - 0.011))) ≤ 0.000609003820 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001431685792 / (12262 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000609003820 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000609003820 : ℝ) + 3.141593 * 0.053427674974 / (12262 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001231848358 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053427674974)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431685792) : PiBarMP 12262 12 0.011 xi bn ≤ 0.164139419316 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12262 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037837624027 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.123194650355 : ℝ) ≤ √((12262 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.733915310531 : ℝ) ≤ √12262 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12262) ≤ 0.125818799270 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037837624027 + 0.053427674974 * 1.772454 / (2 * (110.123194650355 : ℝ))) * (1 + 0.001231848358) +
        8 / (12262 * 110.733915310531) + 0.125818799270 := by gcongr
    _ ≤ (0.164139419316 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053427674974)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431685792) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284567987638) :
    parallelOracle 12262 0.011 xi bn cd ≤ 0.165168089482 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12262 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12262 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560483053099 : ℝ) ≤ plow 12262 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.733915310531 : ℝ) ≤ √12262 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284567987638 : ℝ) / (2 * 0.560483053099 * 110.733915310531)) * 0.164139419316 +
        0.284567987638 ^ 2 / (2 * 0.560483053099 * 110.733915310531) := by gcongr
    _ ≤ (0.165168089482 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053427674974) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001431685792)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284567987638) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12262 12262 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560483053099 : ℝ) ≤ plow 12262 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.733915310531 : ℝ) ≤ √12262 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12262 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12262 Θ 1.22 ≤ 0.011975558674 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 110.733915310531 := by gcongr <;> linarith
      _ ≤ (0.011975558674 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12262 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12262 12262 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12262 12262 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12262 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12262 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12262 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12262 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165168089482 + 0.011975558674 + (0.008646 : ℝ) *
        (1 + 2 * (0.284567987638 + 0.011975558674) / (0.560483053099 * 110.733915310531))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12262]

end BstLean.Part264b.N12262

/-! The original eight local profiles supply actual 12262 moment certificates. -/
namespace BstLean.Part264b.N12262
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12262 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053427674974 ∧
    0 ≤ bN 12262 BstLean.Part154.csC (groupTheta g) ∧ bN 12262 BstLean.Part154.csC (groupTheta g) ≤ 0.001431685792 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12262 12262 0.011
      (momentAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12262 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12262 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12262 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231144273073 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12262 0.011
      (momentAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12262 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12262
/-! The actual computed-centre upper energy formula at 12262. -/
namespace BstLean.Part264b.N12262
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12262

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12262
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12262 cell12262)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086889397103
  | 2 => 0.087860825378
  | 3 => 0.088835036218
  | 4 => 0.089814478897
  | 5 => 0.090802075212
  | 6 => 0.091801284164
  | 7 => 0.092816171743
  | 8 => 0.093851485720
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12262 12262 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12262 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12262

/-! Actual upper energy certificates on all 43 source endpoints at 12262. -/
namespace BstLean.Part264b.N12262
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12262 cell12262)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12262 (gMinus 12262) (1 - (cell12262 i).lower) ≤ 1 ∧
    energyUpper 12262 (gMinus 12262) (BstLean.Part211.gPlus 12262)
      (finiteEnergy 12262 12262 0.011) (1 - (cell12262 i).lower) ≤
      (cell12262 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12262) (by norm_num)
        (q := 1 - (cell12262 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12262,cell12262]) (by norm_num [scalarRow12262,cell12262])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12262,cell12262])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12262

/-! Source-cell containment and simple scalar guards at 12262. -/
namespace BstLean.Part264b.N12262
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12262 cell12262)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12262 ⟨10,by decide⟩).lower ∧ (cell12262 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12262 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12262 ⟨11,by decide⟩).lower ∧ (cell12262 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12262 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12262 ⟨12,by decide⟩).lower ∧ (cell12262 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12262 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12262 ⟨13,by decide⟩).lower ∧ (cell12262 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12262 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12262 ⟨14,by decide⟩).lower ∧ (cell12262 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12262 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12262 ⟨15,by decide⟩).lower ∧ (cell12262 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12262 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12262 ⟨16,by decide⟩).lower ∧ (cell12262 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12262 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12262 ⟨17,by decide⟩).lower ∧ (cell12262 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12262 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12262 ⟨18,by decide⟩).lower ∧ (cell12262 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12262 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12262 ⟨19,by decide⟩).lower ∧ (cell12262 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12262 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12262 ⟨20,by decide⟩).lower ∧ (cell12262 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12262 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12262 ⟨21,by decide⟩).lower ∧ (cell12262 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12262 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12262 ⟨22,by decide⟩).lower ∧ (cell12262 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12262 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12262 ⟨23,by decide⟩).lower ∧ (cell12262 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12262 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12262 ⟨24,by decide⟩).lower ∧ (cell12262 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12262 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12262 ⟨25,by decide⟩).lower ∧ (cell12262 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12262 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12262 ⟨26,by decide⟩).lower ∧ (cell12262 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12262 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12262 ⟨27,by decide⟩).lower ∧ (cell12262 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12262 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12262 ⟨28,by decide⟩).lower ∧ (cell12262 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12262 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12262 ⟨29,by decide⟩).lower ∧ (cell12262 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12262 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12262 ⟨30,by decide⟩).lower ∧ (cell12262 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12262 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12262 ⟨31,by decide⟩).lower ∧ (cell12262 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12262 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12262 ⟨32,by decide⟩).lower ∧ (cell12262 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12262 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12262 ⟨33,by decide⟩).lower ∧ (cell12262 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12262 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12262 ⟨34,by decide⟩).lower ∧ (cell12262 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12262 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12262 ⟨35,by decide⟩).lower ∧ (cell12262 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12262 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12262 ⟨36,by decide⟩).lower ∧ (cell12262 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12262 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12262 ⟨37,by decide⟩).lower ∧ (cell12262 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12262 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12262 ⟨38,by decide⟩).lower ∧ (cell12262 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12262 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12262 ⟨39,by decide⟩).lower ∧ (cell12262 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12262 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12262 ⟨40,by decide⟩).lower ∧ (cell12262 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12262 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12262 ⟨41,by decide⟩).lower ∧ (cell12262 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12262 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12262 ⟨42,by decide⟩).lower ∧ (cell12262 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12262 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12262 ⟨43,by decide⟩).lower ∧ (cell12262 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12262 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12262 ⟨44,by decide⟩).lower ∧ (cell12262 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12262 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12262 ⟨45,by decide⟩).lower ∧ (cell12262 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12262 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12262 ⟨46,by decide⟩).lower ∧ (cell12262 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12262 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12262 ⟨47,by decide⟩).lower ∧ (cell12262 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12262 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12262 ⟨48,by decide⟩).lower ∧ (cell12262 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12262 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12262 ⟨49,by decide⟩).lower ∧ (cell12262 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12262 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12262 ⟨50,by decide⟩).lower ∧ (cell12262 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12262 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12262 ⟨51,by decide⟩).lower ∧ (cell12262 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12262 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12262 ⟨52,by decide⟩).lower ∧ (cell12262 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12262 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12262 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12262 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12262,cell12262,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12262 i).lower ∧
    (cell12262 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12262 i).upper ≤ (0.532 : ℝ) ∧
    (cell12262 i).centre ≤ (0.1 : ℝ) ∧ (cell12262 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12262 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12262 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12262

/-! The local source numeric instances at 12262 have no network premises. -/
namespace BstLean.Part264b.N12262
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12262 cell12262)

noncomputable def sourceNumerics12262 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12262 (cell12262 i)
      scalarRow12262.M scalarRow12262.H scalarRow12262.xi := by
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
    energy_allowance := scalarRow12262.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12262]
    centre_nonneg := (scalarRow12262.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12262]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12262
/-! Actual 12263 scalar aliases and the unchanged imported parallel allowance. -/
