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
namespace BstLean.Part264b.N12338
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12338 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12338 12338 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12338.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12338 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12338 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12338 := gPlus_lower 12338
end BstLean.Part264b.N12338

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12338
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036335402879 : ℝ) ≤ wn 12338 := by
  have hn : √(12338 : ℝ) ≤ 111.076550180495 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12338 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.076550180495 ≤ 2 / √12338 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259402824 : ℝ) ≤ rhoBar 12338 BstLean.Part154.csC ∧
    rhoBar 12338 BstLean.Part154.csC ≤ 0.000259445677 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036335402879 : ℝ) / (1.295212 * 12338) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12338) := by gcongr
      _ ≤ (0.000259445677 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12338 BstLean.Part154.csC) ≤ 0.001037850021 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12338 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12338 BstLean.Part154.csC) (piBar (rhoBar 12338 BstLean.Part154.csC)) ≤ 0.000198166635 ∧
    cc1 (rhoBar 12338 BstLean.Part154.csC) (piBar (rhoBar 12338 BstLean.Part154.csC)) ≤ 0.000126094689 ∧
    cc2 (rhoBar 12338 BstLean.Part154.csC) ≤ 0.000073198864 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12338 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12338 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12338 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12338 BstLean.Part154.csC * nuR (rhoBar 12338 BstLean.Part154.csC)) ≤ 0.000518908182 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259445677 : ℝ) * 0.001037850021 := by gcongr
      _ ≤ (0.000518908182 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12338 BstLean.Part154.csC) * nuR (rhoBar 12338 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037850021 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12338 BstLean.Part154.csC) * rhoBar 12338 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259445677 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259445677 / 2 + 0.399 * 0.001037850021 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198166635 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518908182 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126094689 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259445677 / 1.414213562 := by gcongr
      _ ≤ (0.000073198864 : ℝ) := by norm_num

end BstLean.Part264b.N12338

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12338
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12338 BstLean.Part154.csC) (piBar (rhoBar 12338 BstLean.Part154.csC)) ≤ 1.69588E-7 := by
  have hr0 : 0 ≤ rhoBar 12338 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12338 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12338 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12338 BstLean.Part154.csC) (piBar (rhoBar 12338 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12338 BstLean.Part154.csC) (piBar (rhoBar 12338 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12338 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198166635 : ℝ) ^ 2 + 0.000126094689 ^ 2 + 3 * 0.000073198864 ^ 2 +
        2 * 0.797885 * 0.000198166635 * 0.000126094689 + 2 * 0.000198166635 * 0.000073198864 +
        4 * 0.797885 * 0.000126094689 * 0.000073198864 := by gcongr
    _ ≤ (1.69588E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12338 BstLean.Part154.csC Θ ≤ 0.002710514978 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12338 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12338 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12338 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12338 BstLean.Part154.csC) (piBar (rhoBar 12338 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12338 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69588E-7 / (0.000259402824 : ℝ) := by gcongr
    _ ≤ 0.002710514978 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12338 BstLean.Part154.csC Θ ≤ 0.003008994628 + 0.000684791002 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12338 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12338 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12338 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259445677 +
        (6863 / 10000) * 0.000259445677 * 12338 * 0.001037850021) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003008994628 + 0.000684791002 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12338 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12338 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12338 0.011 Θ ∧ gammaRatio 12338 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12338 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12338) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12338 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12338 0.011 Θ) :=
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
    badAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12338 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12338 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12338 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12338 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12338 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12338 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12338 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12338 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12338 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12338 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12338 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004108994628 + 0.003395305980 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12338

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12338
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12338 BstLean.Part154.csC) (piBar (rhoBar 12338 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12338 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12338 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12338 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12338 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12338 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12338 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12338 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12338 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12338 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12338 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12338 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12338 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053257107236 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12338) ≤ 0.010751482461 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12338 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010751482461 + 2 * 0.737676 / 12338) := by gcongr
    _ ≤ (0.053257107236 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12338 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12338

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12338
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486717255 : ℝ) ≤ plow 12338 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12338) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398130268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423020364) : eMP 12338 0.011 xi bn ≤ 0.001224318073 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12338 : ℝ) * (1 - 0.011))) ≤ 0.000605285109 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001423020364 / (12338 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605285109 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605285109 : ℝ) + 3.141593 * 0.053398130268 / (12338 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001224318073 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398130268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423020364) : PiBarMP 12338 12 0.011 xi bn ≤ 0.163634579370 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12338 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037722942145 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.463939817480 : ℝ) ≤ √((12338 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.076550180494 : ℝ) ≤ √12338 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12338) ≤ 0.125430689377 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037722942145 + 0.053398130268 * 1.772454 / (2 * (110.463939817480 : ℝ))) * (1 + 0.001224318073) +
        8 / (12338 * 111.076550180494) + 0.125430689377 := by gcongr
    _ ≤ (0.163634579370 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398130268)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423020364) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284337461806) :
    parallelOracle 12338 0.011 xi bn cd ≤ 0.164657559713 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12338 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12338 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486717255 : ℝ) ≤ plow 12338 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.076550180494 : ℝ) ≤ √12338 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284337461806 : ℝ) / (2 * 0.560486717255 * 111.076550180494)) * 0.163634579370 +
        0.284337461806 ^ 2 / (2 * 0.560486717255 * 111.076550180494) := by gcongr
    _ ≤ (0.164657559713 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053398130268) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001423020364)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284337461806) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12338 12338 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486717255 : ℝ) ≤ plow 12338 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.076550180494 : ℝ) ≤ √12338 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12338 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12338 Θ 1.22 ≤ 0.011938617988 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.076550180494 := by gcongr <;> linarith
      _ ≤ (0.011938617988 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12338 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12338 12338 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12338 12338 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12338 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12338 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12338 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12338 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164657559713 + 0.011938617988 + (0.008646 : ℝ) *
        (1 + 2 * (0.284337461806 + 0.011938617988) / (0.560486717255 * 111.076550180494))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12338]

end BstLean.Part264b.N12338

/-! The original eight local profiles supply actual 12338 moment certificates. -/
namespace BstLean.Part264b.N12338
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12338 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053398130268 ∧
    0 ≤ bN 12338 BstLean.Part154.csC (groupTheta g) ∧ bN 12338 BstLean.Part154.csC (groupTheta g) ≤ 0.001423020364 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12338 12338 0.011
      (momentAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12338 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12338 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12338 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231080354570 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12338 0.011
      (momentAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12338 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12338
/-! The actual computed-centre upper energy formula at 12338. -/
namespace BstLean.Part264b.N12338
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12338

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12338
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12338 cell12338)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086626777708
  | 2 => 0.087592355760
  | 3 => 0.088559707142
  | 4 => 0.089531062363
  | 5 => 0.090509088231
  | 6 => 0.091496948471
  | 7 => 0.092498369310
  | 8 => 0.093517709935
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12338 12338 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12338 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12338

/-! Actual upper energy certificates on all 43 source endpoints at 12338. -/
namespace BstLean.Part264b.N12338
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12338 cell12338)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12338 (gMinus 12338) (1 - (cell12338 i).lower) ≤ 1 ∧
    energyUpper 12338 (gMinus 12338) (BstLean.Part211.gPlus 12338)
      (finiteEnergy 12338 12338 0.011) (1 - (cell12338 i).lower) ≤
      (cell12338 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12338) (by norm_num)
        (q := 1 - (cell12338 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12338,cell12338]) (by norm_num [scalarRow12338,cell12338])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12338,cell12338])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12338

/-! Source-cell containment and simple scalar guards at 12338. -/
namespace BstLean.Part264b.N12338
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12338 cell12338)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12338 ⟨10,by decide⟩).lower ∧ (cell12338 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12338 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12338 ⟨11,by decide⟩).lower ∧ (cell12338 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12338 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12338 ⟨12,by decide⟩).lower ∧ (cell12338 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12338 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12338 ⟨13,by decide⟩).lower ∧ (cell12338 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12338 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12338 ⟨14,by decide⟩).lower ∧ (cell12338 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12338 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12338 ⟨15,by decide⟩).lower ∧ (cell12338 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12338 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12338 ⟨16,by decide⟩).lower ∧ (cell12338 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12338 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12338 ⟨17,by decide⟩).lower ∧ (cell12338 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12338 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12338 ⟨18,by decide⟩).lower ∧ (cell12338 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12338 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12338 ⟨19,by decide⟩).lower ∧ (cell12338 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12338 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12338 ⟨20,by decide⟩).lower ∧ (cell12338 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12338 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12338 ⟨21,by decide⟩).lower ∧ (cell12338 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12338 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12338 ⟨22,by decide⟩).lower ∧ (cell12338 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12338 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12338 ⟨23,by decide⟩).lower ∧ (cell12338 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12338 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12338 ⟨24,by decide⟩).lower ∧ (cell12338 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12338 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12338 ⟨25,by decide⟩).lower ∧ (cell12338 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12338 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12338 ⟨26,by decide⟩).lower ∧ (cell12338 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12338 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12338 ⟨27,by decide⟩).lower ∧ (cell12338 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12338 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12338 ⟨28,by decide⟩).lower ∧ (cell12338 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12338 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12338 ⟨29,by decide⟩).lower ∧ (cell12338 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12338 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12338 ⟨30,by decide⟩).lower ∧ (cell12338 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12338 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12338 ⟨31,by decide⟩).lower ∧ (cell12338 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12338 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12338 ⟨32,by decide⟩).lower ∧ (cell12338 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12338 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12338 ⟨33,by decide⟩).lower ∧ (cell12338 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12338 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12338 ⟨34,by decide⟩).lower ∧ (cell12338 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12338 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12338 ⟨35,by decide⟩).lower ∧ (cell12338 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12338 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12338 ⟨36,by decide⟩).lower ∧ (cell12338 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12338 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12338 ⟨37,by decide⟩).lower ∧ (cell12338 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12338 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12338 ⟨38,by decide⟩).lower ∧ (cell12338 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12338 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12338 ⟨39,by decide⟩).lower ∧ (cell12338 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12338 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12338 ⟨40,by decide⟩).lower ∧ (cell12338 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12338 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12338 ⟨41,by decide⟩).lower ∧ (cell12338 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12338 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12338 ⟨42,by decide⟩).lower ∧ (cell12338 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12338 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12338 ⟨43,by decide⟩).lower ∧ (cell12338 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12338 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12338 ⟨44,by decide⟩).lower ∧ (cell12338 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12338 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12338 ⟨45,by decide⟩).lower ∧ (cell12338 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12338 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12338 ⟨46,by decide⟩).lower ∧ (cell12338 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12338 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12338 ⟨47,by decide⟩).lower ∧ (cell12338 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12338 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12338 ⟨48,by decide⟩).lower ∧ (cell12338 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12338 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12338 ⟨49,by decide⟩).lower ∧ (cell12338 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12338 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12338 ⟨50,by decide⟩).lower ∧ (cell12338 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12338 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12338 ⟨51,by decide⟩).lower ∧ (cell12338 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12338 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12338 ⟨52,by decide⟩).lower ∧ (cell12338 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12338 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12338 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12338 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12338,cell12338,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12338 i).lower ∧
    (cell12338 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12338 i).upper ≤ (0.532 : ℝ) ∧
    (cell12338 i).centre ≤ (0.1 : ℝ) ∧ (cell12338 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12338 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12338 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12338

/-! The local source numeric instances at 12338 have no network premises. -/
namespace BstLean.Part264b.N12338
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12338 cell12338)

noncomputable def sourceNumerics12338 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12338 (cell12338 i)
      scalarRow12338.M scalarRow12338.H scalarRow12338.xi := by
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
    energy_allowance := scalarRow12338.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12338]
    centre_nonneg := (scalarRow12338.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12338]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12338
/-! Actual 12339 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12339
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12339 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12339 12339 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12339.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12339 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12339 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12339 := gPlus_lower 12339
end BstLean.Part264b.N12339

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12339
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036333917331 : ℝ) ≤ wn 12339 := by
  have hn : √(12339 : ℝ) ≤ 111.081051489442 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12339 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.081051489442 ≤ 2 / √12339 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259381429 : ℝ) ≤ rhoBar 12339 BstLean.Part154.csC ∧
    rhoBar 12339 BstLean.Part154.csC ≤ 0.000259424651 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036333917331 : ℝ) / (1.295212 * 12339) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12339) := by gcongr
      _ ≤ (0.000259424651 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12339 BstLean.Part154.csC) ≤ 0.001037765906 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12339 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12339 BstLean.Part154.csC) (piBar (rhoBar 12339 BstLean.Part154.csC)) ≤ 0.000198150575 ∧
    cc1 (rhoBar 12339 BstLean.Part154.csC) (piBar (rhoBar 12339 BstLean.Part154.csC)) ≤ 0.000126084470 ∧
    cc2 (rhoBar 12339 BstLean.Part154.csC) ≤ 0.000073192932 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12339 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12339 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12339 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12339 BstLean.Part154.csC * nuR (rhoBar 12339 BstLean.Part154.csC)) ≤ 0.000518866128 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259424651 : ℝ) * 0.001037765906 := by gcongr
      _ ≤ (0.000518866128 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12339 BstLean.Part154.csC) * nuR (rhoBar 12339 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037765906 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12339 BstLean.Part154.csC) * rhoBar 12339 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259424651 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259424651 / 2 + 0.399 * 0.001037765906 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198150575 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518866128 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126084470 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259424651 / 1.414213562 := by gcongr
      _ ≤ (0.000073192932 : ℝ) := by norm_num

end BstLean.Part264b.N12339

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12339
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12339 BstLean.Part154.csC) (piBar (rhoBar 12339 BstLean.Part154.csC)) ≤ 1.69561E-7 := by
  have hr0 : 0 ≤ rhoBar 12339 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12339 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12339 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12339 BstLean.Part154.csC) (piBar (rhoBar 12339 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12339 BstLean.Part154.csC) (piBar (rhoBar 12339 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12339 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198150575 : ℝ) ^ 2 + 0.000126084470 ^ 2 + 3 * 0.000073192932 ^ 2 +
        2 * 0.797885 * 0.000198150575 * 0.000126084470 + 2 * 0.000198150575 * 0.000073192932 +
        4 * 0.797885 * 0.000126084470 * 0.000073192932 := by gcongr
    _ ≤ (1.69561E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12339 BstLean.Part154.csC Θ ≤ 0.002710306979 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12339 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12339 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12339 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12339 BstLean.Part154.csC) (piBar (rhoBar 12339 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12339 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69561E-7 / (0.000259381429 : ℝ) := by gcongr
    _ ≤ 0.002710306979 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12339 BstLean.Part154.csC Θ ≤ 0.003008750763 + 0.000684735505 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12339 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12339 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12339 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259424651 +
        (6863 / 10000) * 0.000259424651 * 12339 * 0.001037765906) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003008750763 + 0.000684735505 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12339 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12339 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12339 0.011 Θ ∧ gammaRatio 12339 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12339 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12339) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12339 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12339 0.011 Θ) :=
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
    badAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12339 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12339 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12339 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12339 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12339 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12339 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12339 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12339 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12339 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12339 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12339 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004108750763 + 0.003395042484 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12339

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12339
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12339 BstLean.Part154.csC) (piBar (rhoBar 12339 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12339 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12339 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12339 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12339 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12339 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12339 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12339 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12339 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12339 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12339 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12339 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12339 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053254925377 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12339) ≤ 0.010751046782 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12339 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010751046782 + 2 * 0.737676 / 12339) := by gcongr
    _ ≤ (0.053254925377 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12339 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12339

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12339
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486765167 : ℝ) ≤ plow 12339 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12339) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053397748068)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422911164) : eMP 12339 0.011 xi bn ≤ 0.001224221356 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12339 : ℝ) * (1 - 0.011))) ≤ 0.000605237357 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001422911164 / (12339 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605237357 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605237357 : ℝ) + 3.141593 * 0.053397748068 / (12339 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001224221356 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053397748068)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422911164) : PiBarMP 12339 12 0.011 xi bn ≤ 0.163628022529 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12339 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037721494722 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.468416300768 : ℝ) ≤ √((12339 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.081051489441 : ℝ) ≤ √12339 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12339) ≤ 0.125425606582 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037721494722 + 0.053397748068 * 1.772454 / (2 * (110.468416300768 : ℝ))) * (1 + 0.001224221356) +
        8 / (12339 * 111.081051489441) + 0.125425606582 := by gcongr
    _ ≤ (0.163628022529 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053397748068)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422911164) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284334452961) :
    parallelOracle 12339 0.011 xi bn cd ≤ 0.164650928663 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12339 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12339 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486765167 : ℝ) ≤ plow 12339 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.081051489441 : ℝ) ≤ √12339 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284334452961 : ℝ) / (2 * 0.560486765167 * 111.081051489441)) * 0.163628022529 +
        0.284334452961 ^ 2 / (2 * 0.560486765167 * 111.081051489441) := by gcongr
    _ ≤ (0.164650928663 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053397748068) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422911164)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284334452961) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12339 12339 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486765167 : ℝ) ≤ plow 12339 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.081051489441 : ℝ) ≤ √12339 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12339 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12339 Θ 1.22 ≤ 0.011938134203 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.081051489441 := by gcongr <;> linarith
      _ ≤ (0.011938134203 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12339 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12339 12339 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12339 12339 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12339 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12339 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12339 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12339 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164650928663 + 0.011938134203 + (0.008646 : ℝ) *
        (1 + 2 * (0.284334452961 + 0.011938134203) / (0.560486765167 * 111.081051489441))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12339]

end BstLean.Part264b.N12339

/-! The original eight local profiles supply actual 12339 moment certificates. -/
namespace BstLean.Part264b.N12339
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12339 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053397748068 ∧
    0 ≤ bN 12339 BstLean.Part154.csC (groupTheta g) ∧ bN 12339 BstLean.Part154.csC (groupTheta g) ≤ 0.001422911164 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12339 12339 0.011
      (momentAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12339 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12339 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12339 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231079527584 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12339 0.011
      (momentAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12339 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12339
/-! The actual computed-centre upper energy formula at 12339. -/
namespace BstLean.Part264b.N12339
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12339

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12339
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12339 cell12339)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086623385185
  | 2 => 0.087588889105
  | 3 => 0.088556153734
  | 4 => 0.089527406832
  | 5 => 0.090505311994
  | 6 => 0.091493029227
  | 7 => 0.092494280471
  | 8 => 0.093513420008
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12339 12339 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12339 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12339

/-! Actual upper energy certificates on all 43 source endpoints at 12339. -/
namespace BstLean.Part264b.N12339
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12339 cell12339)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12339 (gMinus 12339) (1 - (cell12339 i).lower) ≤ 1 ∧
    energyUpper 12339 (gMinus 12339) (BstLean.Part211.gPlus 12339)
      (finiteEnergy 12339 12339 0.011) (1 - (cell12339 i).lower) ≤
      (cell12339 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12339) (by norm_num)
        (q := 1 - (cell12339 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12339,cell12339]) (by norm_num [scalarRow12339,cell12339])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12339,cell12339])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12339

/-! Source-cell containment and simple scalar guards at 12339. -/
namespace BstLean.Part264b.N12339
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12339 cell12339)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12339 ⟨10,by decide⟩).lower ∧ (cell12339 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12339 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12339 ⟨11,by decide⟩).lower ∧ (cell12339 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12339 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12339 ⟨12,by decide⟩).lower ∧ (cell12339 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12339 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12339 ⟨13,by decide⟩).lower ∧ (cell12339 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12339 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12339 ⟨14,by decide⟩).lower ∧ (cell12339 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12339 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12339 ⟨15,by decide⟩).lower ∧ (cell12339 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12339 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12339 ⟨16,by decide⟩).lower ∧ (cell12339 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12339 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12339 ⟨17,by decide⟩).lower ∧ (cell12339 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12339 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12339 ⟨18,by decide⟩).lower ∧ (cell12339 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12339 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12339 ⟨19,by decide⟩).lower ∧ (cell12339 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12339 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12339 ⟨20,by decide⟩).lower ∧ (cell12339 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12339 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12339 ⟨21,by decide⟩).lower ∧ (cell12339 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12339 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12339 ⟨22,by decide⟩).lower ∧ (cell12339 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12339 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12339 ⟨23,by decide⟩).lower ∧ (cell12339 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12339 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12339 ⟨24,by decide⟩).lower ∧ (cell12339 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12339 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12339 ⟨25,by decide⟩).lower ∧ (cell12339 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12339 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12339 ⟨26,by decide⟩).lower ∧ (cell12339 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12339 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12339 ⟨27,by decide⟩).lower ∧ (cell12339 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12339 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12339 ⟨28,by decide⟩).lower ∧ (cell12339 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12339 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12339 ⟨29,by decide⟩).lower ∧ (cell12339 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12339 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12339 ⟨30,by decide⟩).lower ∧ (cell12339 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12339 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12339 ⟨31,by decide⟩).lower ∧ (cell12339 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12339 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12339 ⟨32,by decide⟩).lower ∧ (cell12339 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12339 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12339 ⟨33,by decide⟩).lower ∧ (cell12339 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12339 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12339 ⟨34,by decide⟩).lower ∧ (cell12339 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12339 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12339 ⟨35,by decide⟩).lower ∧ (cell12339 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12339 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12339 ⟨36,by decide⟩).lower ∧ (cell12339 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12339 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12339 ⟨37,by decide⟩).lower ∧ (cell12339 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12339 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12339 ⟨38,by decide⟩).lower ∧ (cell12339 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12339 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12339 ⟨39,by decide⟩).lower ∧ (cell12339 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12339 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12339 ⟨40,by decide⟩).lower ∧ (cell12339 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12339 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12339 ⟨41,by decide⟩).lower ∧ (cell12339 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12339 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12339 ⟨42,by decide⟩).lower ∧ (cell12339 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12339 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12339 ⟨43,by decide⟩).lower ∧ (cell12339 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12339 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12339 ⟨44,by decide⟩).lower ∧ (cell12339 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12339 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12339 ⟨45,by decide⟩).lower ∧ (cell12339 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12339 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12339 ⟨46,by decide⟩).lower ∧ (cell12339 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12339 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12339 ⟨47,by decide⟩).lower ∧ (cell12339 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12339 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12339 ⟨48,by decide⟩).lower ∧ (cell12339 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12339 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12339 ⟨49,by decide⟩).lower ∧ (cell12339 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12339 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12339 ⟨50,by decide⟩).lower ∧ (cell12339 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12339 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12339 ⟨51,by decide⟩).lower ∧ (cell12339 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12339 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12339 ⟨52,by decide⟩).lower ∧ (cell12339 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12339 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12339 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12339 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12339,cell12339,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12339 i).lower ∧
    (cell12339 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12339 i).upper ≤ (0.532 : ℝ) ∧
    (cell12339 i).centre ≤ (0.1 : ℝ) ∧ (cell12339 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12339 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12339 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12339

/-! The local source numeric instances at 12339 have no network premises. -/
namespace BstLean.Part264b.N12339
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12339 cell12339)

noncomputable def sourceNumerics12339 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12339 (cell12339 i)
      scalarRow12339.M scalarRow12339.H scalarRow12339.xi := by
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
    energy_allowance := scalarRow12339.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12339]
    centre_nonneg := (scalarRow12339.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12339]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12339
/-! Actual 12340 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12340
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12340 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12340 12340 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12340.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12340 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12340 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12340 := gPlus_lower 12340
end BstLean.Part264b.N12340

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12340
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036332431966 : ℝ) ≤ wn 12340 := by
  have hn : √(12340 : ℝ) ≤ 111.085552615991 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12340 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.085552615991 ≤ 2 / √12340 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259360038 : ℝ) ≤ rhoBar 12340 BstLean.Part154.csC ∧
    rhoBar 12340 BstLean.Part154.csC ≤ 0.000259403628 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036332431966 : ℝ) / (1.295212 * 12340) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12340) := by gcongr
      _ ≤ (0.000259403628 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12340 BstLean.Part154.csC) ≤ 0.001037681803 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12340 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12340 BstLean.Part154.csC) (piBar (rhoBar 12340 BstLean.Part154.csC)) ≤ 0.000198134516 ∧
    cc1 (rhoBar 12340 BstLean.Part154.csC) (piBar (rhoBar 12340 BstLean.Part154.csC)) ≤ 0.000126074252 ∧
    cc2 (rhoBar 12340 BstLean.Part154.csC) ≤ 0.000073187000 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12340 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12340 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12340 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12340 BstLean.Part154.csC * nuR (rhoBar 12340 BstLean.Part154.csC)) ≤ 0.000518824079 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259403628 : ℝ) * 0.001037681803 := by gcongr
      _ ≤ (0.000518824079 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12340 BstLean.Part154.csC) * nuR (rhoBar 12340 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037681803 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12340 BstLean.Part154.csC) * rhoBar 12340 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259403628 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259403628 / 2 + 0.399 * 0.001037681803 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198134516 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518824079 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126074252 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259403628 / 1.414213562 := by gcongr
      _ ≤ (0.000073187000 : ℝ) := by norm_num

end BstLean.Part264b.N12340

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12340
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12340 BstLean.Part154.csC) (piBar (rhoBar 12340 BstLean.Part154.csC)) ≤ 1.69533E-7 := by
  have hr0 : 0 ≤ rhoBar 12340 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12340 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12340 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12340 BstLean.Part154.csC) (piBar (rhoBar 12340 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12340 BstLean.Part154.csC) (piBar (rhoBar 12340 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12340 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198134516 : ℝ) ^ 2 + 0.000126074252 ^ 2 + 3 * 0.000073187000 ^ 2 +
        2 * 0.797885 * 0.000198134516 * 0.000126074252 + 2 * 0.000198134516 * 0.000073187000 +
        4 * 0.797885 * 0.000126074252 * 0.000073187000 := by gcongr
    _ ≤ (1.69533E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12340 BstLean.Part154.csC Θ ≤ 0.002710082919 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12340 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12340 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12340 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12340 BstLean.Part154.csC) (piBar (rhoBar 12340 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12340 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69533E-7 / (0.000259360038 : ℝ) := by gcongr
    _ ≤ 0.002710082919 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12340 BstLean.Part154.csC Θ ≤ 0.003008506927 + 0.000684680016 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12340 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12340 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12340 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259403628 +
        (6863 / 10000) * 0.000259403628 * 12340 * 0.001037681803) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003008506927 + 0.000684680016 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12340 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12340 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12340 0.011 Θ ∧ gammaRatio 12340 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12340 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12340) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12340 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12340 0.011 Θ) :=
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
    badAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12340 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12340 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12340 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12340 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12340 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12340 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12340 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12340 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12340 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12340 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12340 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004108506927 + 0.003394762935 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12340

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12340
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12340 BstLean.Part154.csC) (piBar (rhoBar 12340 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12340 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12340 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12340 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12340 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12340 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12340 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12340 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12340 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12340 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12340 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12340 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12340 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053252743781 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12340) ≤ 0.010750611155 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12340 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010750611155 + 2 * 0.737676 / 12340) := by gcongr
    _ ≤ (0.053252743781 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12340 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12340

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12340
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486813071 : ℝ) ≤ plow 12340 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12340) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053397357468)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422793533) : eMP 12340 0.011 xi bn ≤ 0.001224121059 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12340 : ℝ) * (1 - 0.011))) ≤ 0.000605187816 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001422793533 / (12340 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605187816 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605187816 : ℝ) + 3.141593 * 0.053397357468 / (12340 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001224121059 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053397357468)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422793533) : PiBarMP 12340 12 0.011 xi bn ≤ 0.163621354154 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12340 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037719935486 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.472892602665 : ℝ) ≤ √((12340 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.085552615990 : ℝ) ≤ √12340 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12340) ≤ 0.125420524404 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037719935486 + 0.053397357468 * 1.772454 / (2 * (110.472892602665 : ℝ))) * (1 + 0.001224121059) +
        8 / (12340 * 111.085552615990) + 0.125420524404 := by gcongr
    _ ≤ (0.163621354154 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053397357468)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422793533) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284331426199) :
    parallelOracle 12340 0.011 xi bn cd ≤ 0.164644185727 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12340 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12340 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486813071 : ℝ) ≤ plow 12340 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.085552615990 : ℝ) ≤ √12340 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284331426199 : ℝ) / (2 * 0.560486813071 * 111.085552615990)) * 0.163621354154 +
        0.284331426199 ^ 2 / (2 * 0.560486813071 * 111.085552615990) := by gcongr
    _ ≤ (0.164644185727 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053397357468) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422793533)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284331426199) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12340 12340 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486813071 : ℝ) ≤ plow 12340 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.085552615990 : ℝ) ≤ √12340 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12340 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12340 Θ 1.22 ≤ 0.011937650476 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.085552615990 := by gcongr <;> linarith
      _ ≤ (0.011937650476 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12340 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12340 12340 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12340 12340 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12340 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12340 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12340 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12340 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164644185727 + 0.011937650476 + (0.008646 : ℝ) *
        (1 + 2 * (0.284331426199 + 0.011937650476) / (0.560486813071 * 111.085552615990))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12340]

end BstLean.Part264b.N12340

/-! The original eight local profiles supply actual 12340 moment certificates. -/
namespace BstLean.Part264b.N12340
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12340 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053397357468 ∧
    0 ≤ bN 12340 BstLean.Part154.csC (groupTheta g) ∧ bN 12340 BstLean.Part154.csC (groupTheta g) ≤ 0.001422793533 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12340 12340 0.011
      (momentAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12340 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12340 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12340 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231078682418 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12340 0.011
      (momentAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12340 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12340
/-! The actual computed-centre upper energy formula at 12340. -/
namespace BstLean.Part264b.N12340
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12340

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12340
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12340 cell12340)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086619994252
  | 2 => 0.087585424110
  | 3 => 0.088552602076
  | 4 => 0.089523753157
  | 5 => 0.090501537744
  | 6 => 0.091489112128
  | 7 => 0.092490193969
  | 8 => 0.093509132647
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12340 12340 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12340 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12340

/-! Actual upper energy certificates on all 43 source endpoints at 12340. -/
namespace BstLean.Part264b.N12340
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12340 cell12340)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12340 (gMinus 12340) (1 - (cell12340 i).lower) ≤ 1 ∧
    energyUpper 12340 (gMinus 12340) (BstLean.Part211.gPlus 12340)
      (finiteEnergy 12340 12340 0.011) (1 - (cell12340 i).lower) ≤
      (cell12340 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12340) (by norm_num)
        (q := 1 - (cell12340 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12340,cell12340]) (by norm_num [scalarRow12340,cell12340])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12340,cell12340])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12340

/-! Source-cell containment and simple scalar guards at 12340. -/
namespace BstLean.Part264b.N12340
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12340 cell12340)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12340 ⟨10,by decide⟩).lower ∧ (cell12340 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12340 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12340 ⟨11,by decide⟩).lower ∧ (cell12340 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12340 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12340 ⟨12,by decide⟩).lower ∧ (cell12340 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12340 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12340 ⟨13,by decide⟩).lower ∧ (cell12340 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12340 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12340 ⟨14,by decide⟩).lower ∧ (cell12340 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12340 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12340 ⟨15,by decide⟩).lower ∧ (cell12340 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12340 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12340 ⟨16,by decide⟩).lower ∧ (cell12340 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12340 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12340 ⟨17,by decide⟩).lower ∧ (cell12340 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12340 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12340 ⟨18,by decide⟩).lower ∧ (cell12340 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12340 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12340 ⟨19,by decide⟩).lower ∧ (cell12340 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12340 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12340 ⟨20,by decide⟩).lower ∧ (cell12340 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12340 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12340 ⟨21,by decide⟩).lower ∧ (cell12340 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12340 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12340 ⟨22,by decide⟩).lower ∧ (cell12340 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12340 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12340 ⟨23,by decide⟩).lower ∧ (cell12340 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12340 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12340 ⟨24,by decide⟩).lower ∧ (cell12340 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12340 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12340 ⟨25,by decide⟩).lower ∧ (cell12340 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12340 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12340 ⟨26,by decide⟩).lower ∧ (cell12340 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12340 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12340 ⟨27,by decide⟩).lower ∧ (cell12340 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12340 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12340 ⟨28,by decide⟩).lower ∧ (cell12340 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12340 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12340 ⟨29,by decide⟩).lower ∧ (cell12340 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12340 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12340 ⟨30,by decide⟩).lower ∧ (cell12340 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12340 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12340 ⟨31,by decide⟩).lower ∧ (cell12340 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12340 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12340 ⟨32,by decide⟩).lower ∧ (cell12340 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12340 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12340 ⟨33,by decide⟩).lower ∧ (cell12340 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12340 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12340 ⟨34,by decide⟩).lower ∧ (cell12340 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12340 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12340 ⟨35,by decide⟩).lower ∧ (cell12340 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12340 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12340 ⟨36,by decide⟩).lower ∧ (cell12340 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12340 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12340 ⟨37,by decide⟩).lower ∧ (cell12340 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12340 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12340 ⟨38,by decide⟩).lower ∧ (cell12340 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12340 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12340 ⟨39,by decide⟩).lower ∧ (cell12340 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12340 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12340 ⟨40,by decide⟩).lower ∧ (cell12340 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12340 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12340 ⟨41,by decide⟩).lower ∧ (cell12340 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12340 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12340 ⟨42,by decide⟩).lower ∧ (cell12340 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12340 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12340 ⟨43,by decide⟩).lower ∧ (cell12340 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12340 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12340 ⟨44,by decide⟩).lower ∧ (cell12340 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12340 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12340 ⟨45,by decide⟩).lower ∧ (cell12340 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12340 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12340 ⟨46,by decide⟩).lower ∧ (cell12340 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12340 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12340 ⟨47,by decide⟩).lower ∧ (cell12340 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12340 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12340 ⟨48,by decide⟩).lower ∧ (cell12340 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12340 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12340 ⟨49,by decide⟩).lower ∧ (cell12340 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12340 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12340 ⟨50,by decide⟩).lower ∧ (cell12340 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12340 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12340 ⟨51,by decide⟩).lower ∧ (cell12340 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12340 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12340 ⟨52,by decide⟩).lower ∧ (cell12340 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12340 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12340 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12340 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12340,cell12340,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12340 i).lower ∧
    (cell12340 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12340 i).upper ≤ (0.532 : ℝ) ∧
    (cell12340 i).centre ≤ (0.1 : ℝ) ∧ (cell12340 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12340 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12340 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12340

/-! The local source numeric instances at 12340 have no network premises. -/
namespace BstLean.Part264b.N12340
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12340 cell12340)

noncomputable def sourceNumerics12340 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12340 (cell12340 i)
      scalarRow12340.M scalarRow12340.H scalarRow12340.xi := by
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
    energy_allowance := scalarRow12340.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12340]
    centre_nonneg := (scalarRow12340.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12340]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12340
/-! Actual 12341 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12341
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12341 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12341 12341 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12341.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12341 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12341 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12341 := gPlus_lower 12341
end BstLean.Part264b.N12341

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12341
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036330946782 : ℝ) ≤ wn 12341 := by
  have hn : √(12341 : ℝ) ≤ 111.090053560164 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12341 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.090053560164 ≤ 2 / √12341 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259338650 : ℝ) ≤ rhoBar 12341 BstLean.Part154.csC ∧
    rhoBar 12341 BstLean.Part154.csC ≤ 0.000259382608 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036330946782 : ℝ) / (1.295212 * 12341) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12341) := by gcongr
      _ ≤ (0.000259382608 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12341 BstLean.Part154.csC) ≤ 0.001037597712 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12341 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12341 BstLean.Part154.csC) (piBar (rhoBar 12341 BstLean.Part154.csC)) ≤ 0.000198118460 ∧
    cc1 (rhoBar 12341 BstLean.Part154.csC) (piBar (rhoBar 12341 BstLean.Part154.csC)) ≤ 0.000126064035 ∧
    cc2 (rhoBar 12341 BstLean.Part154.csC) ≤ 0.000073181070 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12341 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12341 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12341 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12341 BstLean.Part154.csC * nuR (rhoBar 12341 BstLean.Part154.csC)) ≤ 0.000518782036 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259382608 : ℝ) * 0.001037597712 := by gcongr
      _ ≤ (0.000518782036 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12341 BstLean.Part154.csC) * nuR (rhoBar 12341 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037597712 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12341 BstLean.Part154.csC) * rhoBar 12341 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259382608 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259382608 / 2 + 0.399 * 0.001037597712 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198118460 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518782036 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126064035 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259382608 / 1.414213562 := by gcongr
      _ ≤ (0.000073181070 : ℝ) := by norm_num

end BstLean.Part264b.N12341

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12341
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12341 BstLean.Part154.csC) (piBar (rhoBar 12341 BstLean.Part154.csC)) ≤ 1.69506E-7 := by
  have hr0 : 0 ≤ rhoBar 12341 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12341 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12341 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12341 BstLean.Part154.csC) (piBar (rhoBar 12341 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12341 BstLean.Part154.csC) (piBar (rhoBar 12341 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12341 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198118460 : ℝ) ^ 2 + 0.000126064035 ^ 2 + 3 * 0.000073181070 ^ 2 +
        2 * 0.797885 * 0.000198118460 * 0.000126064035 + 2 * 0.000198118460 * 0.000073181070 +
        4 * 0.797885 * 0.000126064035 * 0.000073181070 := by gcongr
    _ ≤ (1.69506E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12341 BstLean.Part154.csC Θ ≤ 0.002709874777 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12341 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12341 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12341 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12341 BstLean.Part154.csC) (piBar (rhoBar 12341 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12341 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69506E-7 / (0.000259338650 : ℝ) := by gcongr
    _ ≤ 0.002709874777 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12341 BstLean.Part154.csC Θ ≤ 0.003008263122 + 0.000684624535 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12341 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12341 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12341 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259382608 +
        (6863 / 10000) * 0.000259382608 * 12341 * 0.001037597712) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003008263122 + 0.000684624535 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12341 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12341 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12341 0.011 Θ ∧ gammaRatio 12341 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12341 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12341) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12341 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12341 0.011 Θ) :=
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
    badAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12341 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12341 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12341 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12341 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12341 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12341 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12341 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12341 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12341 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12341 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12341 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004108263122 + 0.003394499312 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12341

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12341
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12341 BstLean.Part154.csC) (piBar (rhoBar 12341 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12341 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12341 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12341 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12341 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12341 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12341 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12341 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12341 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12341 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12341 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12341 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12341 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053250562451 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12341) ≤ 0.010750175581 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12341 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010750175581 + 2 * 0.737676 / 12341) := by gcongr
    _ ≤ (0.053250562451 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12341 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12341

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12341
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486860967 : ℝ) ≤ plow 12341 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12341) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396975261)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422684258) : eMP 12341 0.011 xi bn ≤ 0.001224024329 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12341 : ℝ) * (1 - 0.011))) ≤ 0.000605140057 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001422684258 / (12341 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605140057 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605140057 : ℝ) + 3.141593 * 0.053396975261 / (12341 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001224024329 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396975261)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422684258) : PiBarMP 12341 12 0.011 xi bn ≤ 0.163614797442 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12341 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037718486953 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.477368723191 : ℝ) ≤ √((12341 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.090053560163 : ℝ) ≤ √12341 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12341) ≤ 0.125415442844 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037718486953 + 0.053396975261 * 1.772454 / (2 * (110.477368723191 : ℝ))) * (1 + 0.001224024329) +
        8 / (12341 * 111.090053560163) + 0.125415442844 := by gcongr
    _ ≤ (0.163614797442 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396975261)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422684258) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284328417862) :
    parallelOracle 12341 0.011 xi bn cd ≤ 0.164637554826 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12341 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12341 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486860967 : ℝ) ≤ plow 12341 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.090053560163 : ℝ) ≤ √12341 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284328417862 : ℝ) / (2 * 0.560486860967 * 111.090053560163)) * 0.163614797442 +
        0.284328417862 ^ 2 / (2 * 0.560486860967 * 111.090053560163) := by gcongr
    _ ≤ (0.164637554826 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396975261) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422684258)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284328417862) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12341 12341 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486860967 : ℝ) ≤ plow 12341 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.090053560163 : ℝ) ≤ √12341 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12341 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12341 Θ 1.22 ≤ 0.011937166808 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.090053560163 := by gcongr <;> linarith
      _ ≤ (0.011937166808 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12341 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12341 12341 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12341 12341 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12341 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12341 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12341 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12341 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164637554826 + 0.011937166808 + (0.008646 : ℝ) *
        (1 + 2 * (0.284328417862 + 0.011937166808) / (0.560486860967 * 111.090053560163))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12341]

end BstLean.Part264b.N12341

/-! The original eight local profiles supply actual 12341 moment certificates. -/
namespace BstLean.Part264b.N12341
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12341 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053396975261 ∧
    0 ≤ bN 12341 BstLean.Part154.csC (groupTheta g) ∧ bN 12341 BstLean.Part154.csC (groupTheta g) ≤ 0.001422684258 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12341 12341 0.011
      (momentAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12341 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12341 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12341 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231077855411 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12341 0.011
      (momentAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12341 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12341
/-! The actual computed-centre upper energy formula at 12341. -/
namespace BstLean.Part264b.N12341
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12341

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12341
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12341 cell12341)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086616604906
  | 2 => 0.087581960775
  | 3 => 0.088549052164
  | 4 => 0.089520101336
  | 5 => 0.090497765480
  | 6 => 0.091485197174
  | 7 => 0.092486109801
  | 8 => 0.093504847849
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12341 12341 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12341 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12341

/-! Actual upper energy certificates on all 43 source endpoints at 12341. -/
namespace BstLean.Part264b.N12341
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12341 cell12341)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12341 (gMinus 12341) (1 - (cell12341 i).lower) ≤ 1 ∧
    energyUpper 12341 (gMinus 12341) (BstLean.Part211.gPlus 12341)
      (finiteEnergy 12341 12341 0.011) (1 - (cell12341 i).lower) ≤
      (cell12341 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12341) (by norm_num)
        (q := 1 - (cell12341 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12341,cell12341]) (by norm_num [scalarRow12341,cell12341])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12341,cell12341])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12341

/-! Source-cell containment and simple scalar guards at 12341. -/
namespace BstLean.Part264b.N12341
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12341 cell12341)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12341 ⟨10,by decide⟩).lower ∧ (cell12341 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12341 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12341 ⟨11,by decide⟩).lower ∧ (cell12341 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12341 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12341 ⟨12,by decide⟩).lower ∧ (cell12341 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12341 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12341 ⟨13,by decide⟩).lower ∧ (cell12341 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12341 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12341 ⟨14,by decide⟩).lower ∧ (cell12341 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12341 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12341 ⟨15,by decide⟩).lower ∧ (cell12341 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12341 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12341 ⟨16,by decide⟩).lower ∧ (cell12341 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12341 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12341 ⟨17,by decide⟩).lower ∧ (cell12341 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12341 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12341 ⟨18,by decide⟩).lower ∧ (cell12341 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12341 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12341 ⟨19,by decide⟩).lower ∧ (cell12341 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12341 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12341 ⟨20,by decide⟩).lower ∧ (cell12341 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12341 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12341 ⟨21,by decide⟩).lower ∧ (cell12341 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12341 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12341 ⟨22,by decide⟩).lower ∧ (cell12341 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12341 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12341 ⟨23,by decide⟩).lower ∧ (cell12341 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12341 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12341 ⟨24,by decide⟩).lower ∧ (cell12341 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12341 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12341 ⟨25,by decide⟩).lower ∧ (cell12341 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12341 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12341 ⟨26,by decide⟩).lower ∧ (cell12341 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12341 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12341 ⟨27,by decide⟩).lower ∧ (cell12341 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12341 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12341 ⟨28,by decide⟩).lower ∧ (cell12341 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12341 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12341 ⟨29,by decide⟩).lower ∧ (cell12341 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12341 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12341 ⟨30,by decide⟩).lower ∧ (cell12341 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12341 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12341 ⟨31,by decide⟩).lower ∧ (cell12341 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12341 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12341 ⟨32,by decide⟩).lower ∧ (cell12341 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12341 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12341 ⟨33,by decide⟩).lower ∧ (cell12341 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12341 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12341 ⟨34,by decide⟩).lower ∧ (cell12341 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12341 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12341 ⟨35,by decide⟩).lower ∧ (cell12341 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12341 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12341 ⟨36,by decide⟩).lower ∧ (cell12341 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12341 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12341 ⟨37,by decide⟩).lower ∧ (cell12341 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12341 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12341 ⟨38,by decide⟩).lower ∧ (cell12341 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12341 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12341 ⟨39,by decide⟩).lower ∧ (cell12341 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12341 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12341 ⟨40,by decide⟩).lower ∧ (cell12341 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12341 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12341 ⟨41,by decide⟩).lower ∧ (cell12341 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12341 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12341 ⟨42,by decide⟩).lower ∧ (cell12341 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12341 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12341 ⟨43,by decide⟩).lower ∧ (cell12341 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12341 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12341 ⟨44,by decide⟩).lower ∧ (cell12341 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12341 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12341 ⟨45,by decide⟩).lower ∧ (cell12341 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12341 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12341 ⟨46,by decide⟩).lower ∧ (cell12341 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12341 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12341 ⟨47,by decide⟩).lower ∧ (cell12341 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12341 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12341 ⟨48,by decide⟩).lower ∧ (cell12341 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12341 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12341 ⟨49,by decide⟩).lower ∧ (cell12341 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12341 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12341 ⟨50,by decide⟩).lower ∧ (cell12341 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12341 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12341 ⟨51,by decide⟩).lower ∧ (cell12341 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12341 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12341 ⟨52,by decide⟩).lower ∧ (cell12341 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12341 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12341 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12341 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12341,cell12341,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12341 i).lower ∧
    (cell12341 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12341 i).upper ≤ (0.532 : ℝ) ∧
    (cell12341 i).centre ≤ (0.1 : ℝ) ∧ (cell12341 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12341 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12341 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12341

/-! The local source numeric instances at 12341 have no network premises. -/
namespace BstLean.Part264b.N12341
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12341 cell12341)

noncomputable def sourceNumerics12341 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12341 (cell12341 i)
      scalarRow12341.M scalarRow12341.H scalarRow12341.xi := by
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
    energy_allowance := scalarRow12341.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12341]
    centre_nonneg := (scalarRow12341.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12341]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12341
/-! Actual 12342 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12342
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12342 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12342 12342 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12342.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12342 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12342 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12342 := gPlus_lower 12342
end BstLean.Part264b.N12342

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12342
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036329461779 : ℝ) ≤ wn 12342 := by
  have hn : √(12342 : ℝ) ≤ 111.094554321983 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12342 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.094554321983 ≤ 2 / √12342 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259317266 : ℝ) ≤ rhoBar 12342 BstLean.Part154.csC ∧
    rhoBar 12342 BstLean.Part154.csC ≤ 0.000259361592 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036329461779 : ℝ) / (1.295212 * 12342) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12342) := by gcongr
      _ ≤ (0.000259361592 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12342 BstLean.Part154.csC) ≤ 0.001037513637 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12342 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12342 BstLean.Part154.csC) (piBar (rhoBar 12342 BstLean.Part154.csC)) ≤ 0.000198102407 ∧
    cc1 (rhoBar 12342 BstLean.Part154.csC) (piBar (rhoBar 12342 BstLean.Part154.csC)) ≤ 0.000126053821 ∧
    cc2 (rhoBar 12342 BstLean.Part154.csC) ≤ 0.000073175140 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12342 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12342 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12342 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12342 BstLean.Part154.csC * nuR (rhoBar 12342 BstLean.Part154.csC)) ≤ 0.000518740001 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259361592 : ℝ) * 0.001037513637 := by gcongr
      _ ≤ (0.000518740001 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12342 BstLean.Part154.csC) * nuR (rhoBar 12342 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037513637 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12342 BstLean.Part154.csC) * rhoBar 12342 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259361592 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259361592 / 2 + 0.399 * 0.001037513637 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198102407 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518740001 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126053821 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259361592 / 1.414213562 := by gcongr
      _ ≤ (0.000073175140 : ℝ) := by norm_num

end BstLean.Part264b.N12342

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12342
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12342 BstLean.Part154.csC) (piBar (rhoBar 12342 BstLean.Part154.csC)) ≤ 1.69478E-7 := by
  have hr0 : 0 ≤ rhoBar 12342 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12342 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12342 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12342 BstLean.Part154.csC) (piBar (rhoBar 12342 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12342 BstLean.Part154.csC) (piBar (rhoBar 12342 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12342 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198102407 : ℝ) ^ 2 + 0.000126053821 ^ 2 + 3 * 0.000073175140 ^ 2 +
        2 * 0.797885 * 0.000198102407 * 0.000126053821 + 2 * 0.000198102407 * 0.000073175140 +
        4 * 0.797885 * 0.000126053821 * 0.000073175140 := by gcongr
    _ ≤ (1.69478E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12342 BstLean.Part154.csC Θ ≤ 0.002709650570 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12342 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12342 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12342 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12342 BstLean.Part154.csC) (piBar (rhoBar 12342 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12342 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69478E-7 / (0.000259317266 : ℝ) := by gcongr
    _ ≤ 0.002709650570 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12342 BstLean.Part154.csC Θ ≤ 0.003008019370 + 0.000684569065 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12342 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12342 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12342 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259361592 +
        (6863 / 10000) * 0.000259361592 * 12342 * 0.001037513637) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003008019370 + 0.000684569065 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12342 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12342 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12342 0.011 Θ ∧ gammaRatio 12342 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12342 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12342) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12342 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12342 0.011 Θ) :=
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
    badAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12342 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12342 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12342 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12342 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12342 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12342 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12342 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12342 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12342 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12342 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12342 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004108019370 + 0.003394219635 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12342

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12342
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12342 BstLean.Part154.csC) (piBar (rhoBar 12342 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12342 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12342 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12342 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12342 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12342 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12342 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12342 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12342 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12342 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12342 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12342 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12342 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053248381394 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12342) ≤ 0.010749740061 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12342 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010749740061 + 2 * 0.737676 / 12342) := by gcongr
    _ ≤ (0.053248381394 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12342 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12342

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12342
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486908855 : ℝ) ≤ plow 12342 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12342) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396584679)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422566550) : eMP 12342 0.011 xi bn ≤ 0.001223924017 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12342 : ℝ) * (1 - 0.011))) ≤ 0.000605090508 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001422566550 / (12342 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605090508 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605090508 : ℝ) + 3.141593 * 0.053396584679 / (12342 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001223924017 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396584679)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422566550) : PiBarMP 12342 12 0.011 xi bn ≤ 0.163608129162 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12342 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037716926572 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.481844662369 : ℝ) ≤ √((12342 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.094554321982 : ℝ) ≤ √12342 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12342) ≤ 0.125410361902 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037716926572 + 0.053396584679 * 1.772454 / (2 * (110.481844662369 : ℝ))) * (1 + 0.001223924017) +
        8 / (12342 * 111.094554321982) + 0.125410361902 := by gcongr
    _ ≤ (0.163608129162 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396584679)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422566550) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284325391672) :
    parallelOracle 12342 0.011 xi bn cd ≤ 0.164630812005 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12342 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12342 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486908855 : ℝ) ≤ plow 12342 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.094554321982 : ℝ) ≤ √12342 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284325391672 : ℝ) / (2 * 0.560486908855 * 111.094554321982)) * 0.163608129162 +
        0.284325391672 ^ 2 / (2 * 0.560486908855 * 111.094554321982) := by gcongr
    _ ≤ (0.164630812005 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396584679) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422566550)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284325391672) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12342 12342 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486908855 : ℝ) ≤ plow 12342 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.094554321982 : ℝ) ≤ √12342 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12342 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12342 Θ 1.22 ≤ 0.011936683199 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.094554321982 := by gcongr <;> linarith
      _ ≤ (0.011936683199 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12342 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12342 12342 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12342 12342 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12342 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12342 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12342 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12342 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164630812005 + 0.011936683199 + (0.008646 : ℝ) *
        (1 + 2 * (0.284325391672 + 0.011936683199) / (0.560486908855 * 111.094554321982))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12342]

end BstLean.Part264b.N12342

/-! The original eight local profiles supply actual 12342 moment certificates. -/
namespace BstLean.Part264b.N12342
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12342 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053396584679 ∧
    0 ≤ bN 12342 BstLean.Part154.csC (groupTheta g) ∧ bN 12342 BstLean.Part154.csC (groupTheta g) ≤ 0.001422566550 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12342 12342 0.011
      (momentAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12342 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12342 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12342 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231077010278 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12342 0.011
      (momentAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12342 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12342
/-! The actual computed-centre upper energy formula at 12342. -/
namespace BstLean.Part264b.N12342
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12342

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12342
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12342 cell12342)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086613217146
  | 2 => 0.087578499097
  | 3 => 0.088545503996
  | 4 => 0.089516451368
  | 5 => 0.090493995199
  | 6 => 0.091481284361
  | 7 => 0.092482027966
  | 8 => 0.093500565610
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12342 12342 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12342 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12342

/-! Actual upper energy certificates on all 43 source endpoints at 12342. -/
namespace BstLean.Part264b.N12342
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12342 cell12342)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12342 (gMinus 12342) (1 - (cell12342 i).lower) ≤ 1 ∧
    energyUpper 12342 (gMinus 12342) (BstLean.Part211.gPlus 12342)
      (finiteEnergy 12342 12342 0.011) (1 - (cell12342 i).lower) ≤
      (cell12342 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12342) (by norm_num)
        (q := 1 - (cell12342 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12342,cell12342]) (by norm_num [scalarRow12342,cell12342])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12342,cell12342])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12342

/-! Source-cell containment and simple scalar guards at 12342. -/
namespace BstLean.Part264b.N12342
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12342 cell12342)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12342 ⟨10,by decide⟩).lower ∧ (cell12342 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12342 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12342 ⟨11,by decide⟩).lower ∧ (cell12342 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12342 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12342 ⟨12,by decide⟩).lower ∧ (cell12342 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12342 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12342 ⟨13,by decide⟩).lower ∧ (cell12342 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12342 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12342 ⟨14,by decide⟩).lower ∧ (cell12342 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12342 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12342 ⟨15,by decide⟩).lower ∧ (cell12342 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12342 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12342 ⟨16,by decide⟩).lower ∧ (cell12342 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12342 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12342 ⟨17,by decide⟩).lower ∧ (cell12342 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12342 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12342 ⟨18,by decide⟩).lower ∧ (cell12342 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12342 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12342 ⟨19,by decide⟩).lower ∧ (cell12342 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12342 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12342 ⟨20,by decide⟩).lower ∧ (cell12342 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12342 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12342 ⟨21,by decide⟩).lower ∧ (cell12342 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12342 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12342 ⟨22,by decide⟩).lower ∧ (cell12342 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12342 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12342 ⟨23,by decide⟩).lower ∧ (cell12342 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12342 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12342 ⟨24,by decide⟩).lower ∧ (cell12342 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12342 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12342 ⟨25,by decide⟩).lower ∧ (cell12342 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12342 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12342 ⟨26,by decide⟩).lower ∧ (cell12342 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12342 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12342 ⟨27,by decide⟩).lower ∧ (cell12342 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12342 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12342 ⟨28,by decide⟩).lower ∧ (cell12342 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12342 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12342 ⟨29,by decide⟩).lower ∧ (cell12342 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12342 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12342 ⟨30,by decide⟩).lower ∧ (cell12342 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12342 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12342 ⟨31,by decide⟩).lower ∧ (cell12342 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12342 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12342 ⟨32,by decide⟩).lower ∧ (cell12342 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12342 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12342 ⟨33,by decide⟩).lower ∧ (cell12342 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12342 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12342 ⟨34,by decide⟩).lower ∧ (cell12342 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12342 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12342 ⟨35,by decide⟩).lower ∧ (cell12342 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12342 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12342 ⟨36,by decide⟩).lower ∧ (cell12342 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12342 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12342 ⟨37,by decide⟩).lower ∧ (cell12342 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12342 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12342 ⟨38,by decide⟩).lower ∧ (cell12342 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12342 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12342 ⟨39,by decide⟩).lower ∧ (cell12342 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12342 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12342 ⟨40,by decide⟩).lower ∧ (cell12342 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12342 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12342 ⟨41,by decide⟩).lower ∧ (cell12342 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12342 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12342 ⟨42,by decide⟩).lower ∧ (cell12342 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12342 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12342 ⟨43,by decide⟩).lower ∧ (cell12342 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12342 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12342 ⟨44,by decide⟩).lower ∧ (cell12342 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12342 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12342 ⟨45,by decide⟩).lower ∧ (cell12342 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12342 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12342 ⟨46,by decide⟩).lower ∧ (cell12342 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12342 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12342 ⟨47,by decide⟩).lower ∧ (cell12342 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12342 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12342 ⟨48,by decide⟩).lower ∧ (cell12342 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12342 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12342 ⟨49,by decide⟩).lower ∧ (cell12342 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12342 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12342 ⟨50,by decide⟩).lower ∧ (cell12342 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12342 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12342 ⟨51,by decide⟩).lower ∧ (cell12342 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12342 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12342 ⟨52,by decide⟩).lower ∧ (cell12342 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12342 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12342 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12342 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12342,cell12342,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12342 i).lower ∧
    (cell12342 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12342 i).upper ≤ (0.532 : ℝ) ∧
    (cell12342 i).centre ≤ (0.1 : ℝ) ∧ (cell12342 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12342 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12342 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12342

/-! The local source numeric instances at 12342 have no network premises. -/
namespace BstLean.Part264b.N12342
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12342 cell12342)

noncomputable def sourceNumerics12342 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12342 (cell12342 i)
      scalarRow12342.M scalarRow12342.H scalarRow12342.xi := by
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
    energy_allowance := scalarRow12342.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12342]
    centre_nonneg := (scalarRow12342.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12342]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12342
/-! Actual 12343 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12343
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12343 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12343 12343 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12343.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12343 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12343 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12343 := gPlus_lower 12343
end BstLean.Part264b.N12343

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12343
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036327976959 : ℝ) ≤ wn 12343 := by
  have hn : √(12343 : ℝ) ≤ 111.099054901471 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12343 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.099054901471 ≤ 2 / √12343 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259295885 : ℝ) ≤ rhoBar 12343 BstLean.Part154.csC ∧
    rhoBar 12343 BstLean.Part154.csC ≤ 0.000259340579 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036327976959 : ℝ) / (1.295212 * 12343) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12343) := by gcongr
      _ ≤ (0.000259340579 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12343 BstLean.Part154.csC) ≤ 0.001037429574 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12343 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12343 BstLean.Part154.csC) (piBar (rhoBar 12343 BstLean.Part154.csC)) ≤ 0.000198086357 ∧
    cc1 (rhoBar 12343 BstLean.Part154.csC) (piBar (rhoBar 12343 BstLean.Part154.csC)) ≤ 0.000126043608 ∧
    cc2 (rhoBar 12343 BstLean.Part154.csC) ≤ 0.000073169212 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12343 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12343 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12343 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12343 BstLean.Part154.csC * nuR (rhoBar 12343 BstLean.Part154.csC)) ≤ 0.000518697973 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259340579 : ℝ) * 0.001037429574 := by gcongr
      _ ≤ (0.000518697973 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12343 BstLean.Part154.csC) * nuR (rhoBar 12343 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037429574 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12343 BstLean.Part154.csC) * rhoBar 12343 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259340579 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259340579 / 2 + 0.399 * 0.001037429574 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198086357 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518697973 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126043608 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259340579 / 1.414213562 := by gcongr
      _ ≤ (0.000073169212 : ℝ) := by norm_num

end BstLean.Part264b.N12343

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12343
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12343 BstLean.Part154.csC) (piBar (rhoBar 12343 BstLean.Part154.csC)) ≤ 1.69451E-7 := by
  have hr0 : 0 ≤ rhoBar 12343 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12343 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12343 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12343 BstLean.Part154.csC) (piBar (rhoBar 12343 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12343 BstLean.Part154.csC) (piBar (rhoBar 12343 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12343 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198086357 : ℝ) ^ 2 + 0.000126043608 ^ 2 + 3 * 0.000073169212 ^ 2 +
        2 * 0.797885 * 0.000198086357 * 0.000126043608 + 2 * 0.000198086357 * 0.000073169212 +
        4 * 0.797885 * 0.000126043608 * 0.000073169212 := by gcongr
    _ ≤ (1.69451E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12343 BstLean.Part154.csC Θ ≤ 0.002709442285 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12343 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12343 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12343 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12343 BstLean.Part154.csC) (piBar (rhoBar 12343 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12343 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69451E-7 / (0.000259295885 : ℝ) := by gcongr
    _ ≤ 0.002709442285 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12343 BstLean.Part154.csC Θ ≤ 0.003007775648 + 0.000684513602 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12343 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12343 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12343 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259340579 +
        (6863 / 10000) * 0.000259340579 * 12343 * 0.001037429574) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003007775648 + 0.000684513602 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12343 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12343 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12343 0.011 Θ ∧ gammaRatio 12343 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12343 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12343) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12343 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12343 0.011 Θ) :=
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
    badAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12343 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12343 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12343 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12343 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12343 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12343 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12343 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12343 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12343 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12343 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12343 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004107775648 + 0.003393955887 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12343

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12343
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12343 BstLean.Part154.csC) (piBar (rhoBar 12343 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12343 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12343 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12343 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12343 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12343 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12343 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12343 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12343 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12343 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12343 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12343 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12343 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053246200600 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12343) ≤ 0.010749304593 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12343 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010749304593 + 2 * 0.737676 / 12343) := by gcongr
    _ ≤ (0.053246200600 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12343 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12343

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12343
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560486956736 : ℝ) ≤ plow 12343 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12343) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396202489)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422457200) : eMP 12343 0.011 xi bn ≤ 0.001223827269 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12343 : ℝ) * (1 - 0.011))) ≤ 0.000605042740 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001422457200 / (12343 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000605042740 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000605042740 : ℝ) + 3.141593 * 0.053396202489 / (12343 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001223827269 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396202489)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422457200) : PiBarMP 12343 12 0.011 xi bn ≤ 0.163601572580 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12343 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037715476930 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.486320420222 : ℝ) ≤ √((12343 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.099054901470 : ℝ) ≤ √12343 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12343) ≤ 0.125405281577 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037715476930 + 0.053396202489 * 1.772454 / (2 * (110.486320420222 : ℝ))) * (1 + 0.001223827269) +
        8 / (12343 * 111.099054901470) + 0.125405281577 := by gcongr
    _ ≤ (0.163601572580 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396202489)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422457200) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284322383902) :
    parallelOracle 12343 0.011 xi bn cd ≤ 0.164624181254 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12343 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12343 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560486956736 : ℝ) ≤ plow 12343 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.099054901470 : ℝ) ≤ √12343 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284322383902 : ℝ) / (2 * 0.560486956736 * 111.099054901470)) * 0.163601572580 +
        0.284322383902 ^ 2 / (2 * 0.560486956736 * 111.099054901470) := by gcongr
    _ ≤ (0.164624181254 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053396202489) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422457200)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284322383902) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12343 12343 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560486956736 : ℝ) ≤ plow 12343 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.099054901470 : ℝ) ≤ √12343 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12343 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12343 Θ 1.22 ≤ 0.011936199648 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.099054901470 := by gcongr <;> linarith
      _ ≤ (0.011936199648 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12343 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12343 12343 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12343 12343 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12343 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12343 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12343 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12343 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164624181254 + 0.011936199648 + (0.008646 : ℝ) *
        (1 + 2 * (0.284322383902 + 0.011936199648) / (0.560486956736 * 111.099054901470))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12343]

end BstLean.Part264b.N12343

/-! The original eight local profiles supply actual 12343 moment certificates. -/
namespace BstLean.Part264b.N12343
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12343 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053396202489 ∧
    0 ≤ bN 12343 BstLean.Part154.csC (groupTheta g) ∧ bN 12343 BstLean.Part154.csC (groupTheta g) ≤ 0.001422457200 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12343 12343 0.011
      (momentAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12343 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12343 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12343 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231076183302 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12343 0.011
      (momentAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12343 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12343
/-! The actual computed-centre upper energy formula at 12343. -/
namespace BstLean.Part264b.N12343
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12343

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12343
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12343 cell12343)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086609830971
  | 2 => 0.087575039074
  | 3 => 0.088541957572
  | 4 => 0.089512803249
  | 5 => 0.090490226899
  | 6 => 0.091477373687
  | 7 => 0.092477948459
  | 8 => 0.093496285929
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12343 12343 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12343 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12343

/-! Actual upper energy certificates on all 43 source endpoints at 12343. -/
namespace BstLean.Part264b.N12343
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12343 cell12343)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12343 (gMinus 12343) (1 - (cell12343 i).lower) ≤ 1 ∧
    energyUpper 12343 (gMinus 12343) (BstLean.Part211.gPlus 12343)
      (finiteEnergy 12343 12343 0.011) (1 - (cell12343 i).lower) ≤
      (cell12343 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12343) (by norm_num)
        (q := 1 - (cell12343 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12343,cell12343]) (by norm_num [scalarRow12343,cell12343])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12343,cell12343])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12343

/-! Source-cell containment and simple scalar guards at 12343. -/
namespace BstLean.Part264b.N12343
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12343 cell12343)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12343 ⟨10,by decide⟩).lower ∧ (cell12343 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12343 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12343 ⟨11,by decide⟩).lower ∧ (cell12343 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12343 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12343 ⟨12,by decide⟩).lower ∧ (cell12343 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12343 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12343 ⟨13,by decide⟩).lower ∧ (cell12343 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12343 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12343 ⟨14,by decide⟩).lower ∧ (cell12343 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12343 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12343 ⟨15,by decide⟩).lower ∧ (cell12343 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12343 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12343 ⟨16,by decide⟩).lower ∧ (cell12343 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12343 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12343 ⟨17,by decide⟩).lower ∧ (cell12343 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12343 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12343 ⟨18,by decide⟩).lower ∧ (cell12343 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12343 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12343 ⟨19,by decide⟩).lower ∧ (cell12343 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12343 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12343 ⟨20,by decide⟩).lower ∧ (cell12343 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12343 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12343 ⟨21,by decide⟩).lower ∧ (cell12343 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12343 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12343 ⟨22,by decide⟩).lower ∧ (cell12343 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12343 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12343 ⟨23,by decide⟩).lower ∧ (cell12343 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12343 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12343 ⟨24,by decide⟩).lower ∧ (cell12343 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12343 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12343 ⟨25,by decide⟩).lower ∧ (cell12343 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12343 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12343 ⟨26,by decide⟩).lower ∧ (cell12343 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12343 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12343 ⟨27,by decide⟩).lower ∧ (cell12343 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12343 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12343 ⟨28,by decide⟩).lower ∧ (cell12343 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12343 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12343 ⟨29,by decide⟩).lower ∧ (cell12343 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12343 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12343 ⟨30,by decide⟩).lower ∧ (cell12343 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12343 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12343 ⟨31,by decide⟩).lower ∧ (cell12343 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12343 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12343 ⟨32,by decide⟩).lower ∧ (cell12343 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12343 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12343 ⟨33,by decide⟩).lower ∧ (cell12343 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12343 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12343 ⟨34,by decide⟩).lower ∧ (cell12343 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12343 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12343 ⟨35,by decide⟩).lower ∧ (cell12343 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12343 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12343 ⟨36,by decide⟩).lower ∧ (cell12343 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12343 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12343 ⟨37,by decide⟩).lower ∧ (cell12343 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12343 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12343 ⟨38,by decide⟩).lower ∧ (cell12343 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12343 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12343 ⟨39,by decide⟩).lower ∧ (cell12343 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12343 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12343 ⟨40,by decide⟩).lower ∧ (cell12343 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12343 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12343 ⟨41,by decide⟩).lower ∧ (cell12343 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12343 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12343 ⟨42,by decide⟩).lower ∧ (cell12343 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12343 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12343 ⟨43,by decide⟩).lower ∧ (cell12343 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12343 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12343 ⟨44,by decide⟩).lower ∧ (cell12343 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12343 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12343 ⟨45,by decide⟩).lower ∧ (cell12343 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12343 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12343 ⟨46,by decide⟩).lower ∧ (cell12343 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12343 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12343 ⟨47,by decide⟩).lower ∧ (cell12343 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12343 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12343 ⟨48,by decide⟩).lower ∧ (cell12343 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12343 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12343 ⟨49,by decide⟩).lower ∧ (cell12343 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12343 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12343 ⟨50,by decide⟩).lower ∧ (cell12343 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12343 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12343 ⟨51,by decide⟩).lower ∧ (cell12343 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12343 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12343 ⟨52,by decide⟩).lower ∧ (cell12343 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12343 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12343 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12343 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12343,cell12343,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12343 i).lower ∧
    (cell12343 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12343 i).upper ≤ (0.532 : ℝ) ∧
    (cell12343 i).centre ≤ (0.1 : ℝ) ∧ (cell12343 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12343 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12343 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12343

/-! The local source numeric instances at 12343 have no network premises. -/
namespace BstLean.Part264b.N12343
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12343 cell12343)

noncomputable def sourceNumerics12343 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12343 (cell12343 i)
      scalarRow12343.M scalarRow12343.H scalarRow12343.xi := by
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
    energy_allowance := scalarRow12343.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12343]
    centre_nonneg := (scalarRow12343.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12343]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12343
/-! Actual 12344 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12344
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12344 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12344 12344 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12344.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12344 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12344 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12344 := gPlus_lower 12344
end BstLean.Part264b.N12344

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12344
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036326492319 : ℝ) ≤ wn 12344 := by
  have hn : √(12344 : ℝ) ≤ 111.103555298650 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12344 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.103555298650 ≤ 2 / √12344 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259274508 : ℝ) ≤ rhoBar 12344 BstLean.Part154.csC ∧
    rhoBar 12344 BstLean.Part154.csC ≤ 0.000259319569 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036326492319 : ℝ) / (1.295212 * 12344) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12344) := by gcongr
      _ ≤ (0.000259319569 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12344 BstLean.Part154.csC) ≤ 0.001037345523 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12344 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12344 BstLean.Part154.csC) (piBar (rhoBar 12344 BstLean.Part154.csC)) ≤ 0.000198070308 ∧
    cc1 (rhoBar 12344 BstLean.Part154.csC) (piBar (rhoBar 12344 BstLean.Part154.csC)) ≤ 0.000126033396 ∧
    cc2 (rhoBar 12344 BstLean.Part154.csC) ≤ 0.000073163284 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12344 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12344 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12344 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12344 BstLean.Part154.csC * nuR (rhoBar 12344 BstLean.Part154.csC)) ≤ 0.000518655950 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259319569 : ℝ) * 0.001037345523 := by gcongr
      _ ≤ (0.000518655950 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12344 BstLean.Part154.csC) * nuR (rhoBar 12344 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037345523 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12344 BstLean.Part154.csC) * rhoBar 12344 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259319569 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259319569 / 2 + 0.399 * 0.001037345523 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198070308 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518655950 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126033396 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259319569 / 1.414213562 := by gcongr
      _ ≤ (0.000073163284 : ℝ) := by norm_num

end BstLean.Part264b.N12344

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12344
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12344 BstLean.Part154.csC) (piBar (rhoBar 12344 BstLean.Part154.csC)) ≤ 1.69424E-7 := by
  have hr0 : 0 ≤ rhoBar 12344 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12344 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12344 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12344 BstLean.Part154.csC) (piBar (rhoBar 12344 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12344 BstLean.Part154.csC) (piBar (rhoBar 12344 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12344 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198070308 : ℝ) ^ 2 + 0.000126033396 ^ 2 + 3 * 0.000073163284 ^ 2 +
        2 * 0.797885 * 0.000198070308 * 0.000126033396 + 2 * 0.000198070308 * 0.000073163284 +
        4 * 0.797885 * 0.000126033396 * 0.000073163284 := by gcongr
    _ ≤ (1.69424E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12344 BstLean.Part154.csC Θ ≤ 0.002709233924 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12344 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12344 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12344 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12344 BstLean.Part154.csC) (piBar (rhoBar 12344 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12344 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69424E-7 / (0.000259274508 : ℝ) := by gcongr
    _ ≤ 0.002709233924 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12344 BstLean.Part154.csC Θ ≤ 0.003007531956 + 0.000684458147 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12344 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12344 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12344 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259319569 +
        (6863 / 10000) * 0.000259319569 * 12344 * 0.001037345523) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003007531956 + 0.000684458147 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12344 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12344 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12344 0.011 Θ ∧ gammaRatio 12344 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12344 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12344) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12344 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12344 0.011 Θ) :=
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
    badAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12344 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12344 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12344 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12344 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12344 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12344 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12344 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12344 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12344 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12344 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12344 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004107531956 + 0.003393692071 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12344

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12344
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12344 BstLean.Part154.csC) (piBar (rhoBar 12344 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12344 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12344 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12344 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12344 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12344 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12344 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12344 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12344 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12344 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12344 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12344 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12344 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053244020073 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12344) ≤ 0.010748869178 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12344 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010748869178 + 2 * 0.737676 / 12344) := by gcongr
    _ ≤ (0.053244020073 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12344 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12344

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12344
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487004609 : ℝ) ≤ plow 12344 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12344) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395820294)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422347811) : eMP 12344 0.011 xi bn ≤ 0.001223730514 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12344 : ℝ) * (1 - 0.011))) ≤ 0.000604994968 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001422347811 / (12344 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604994968 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604994968 : ℝ) + 3.141593 * 0.053395820294 / (12344 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001223730514 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395820294)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422347811) : PiBarMP 12344 12 0.011 xi bn ≤ 0.163595016044 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12344 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037714026715 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.490795996770 : ℝ) ≤ √((12344 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.103555298649 : ℝ) ≤ √12344 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12344) ≤ 0.125400201869 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037714026715 + 0.053395820294 * 1.772454 / (2 * (110.490795996770 : ℝ))) * (1 + 0.001223730514) +
        8 / (12344 * 111.103555298649) + 0.125400201869 := by gcongr
    _ ≤ (0.163595016044 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395820294)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422347811) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284319376384) :
    parallelOracle 12344 0.011 xi bn cd ≤ 0.164617550558 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12344 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12344 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487004609 : ℝ) ≤ plow 12344 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.103555298649 : ℝ) ≤ √12344 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284319376384 : ℝ) / (2 * 0.560487004609 * 111.103555298649)) * 0.163595016044 +
        0.284319376384 ^ 2 / (2 * 0.560487004609 * 111.103555298649) := by gcongr
    _ ≤ (0.164617550558 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395820294) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422347811)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284319376384) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12344 12344 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487004609 : ℝ) ≤ plow 12344 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.103555298649 : ℝ) ≤ √12344 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12344 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12344 Θ 1.22 ≤ 0.011935716157 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.103555298649 := by gcongr <;> linarith
      _ ≤ (0.011935716157 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12344 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12344 12344 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12344 12344 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12344 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12344 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12344 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12344 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164617550558 + 0.011935716157 + (0.008646 : ℝ) *
        (1 + 2 * (0.284319376384 + 0.011935716157) / (0.560487004609 * 111.103555298649))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12344]

end BstLean.Part264b.N12344

/-! The original eight local profiles supply actual 12344 moment certificates. -/
namespace BstLean.Part264b.N12344
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12344 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053395820294 ∧
    0 ≤ bN 12344 BstLean.Part154.csC (groupTheta g) ∧ bN 12344 BstLean.Part154.csC (groupTheta g) ≤ 0.001422347811 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12344 12344 0.011
      (momentAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12344 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12344 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12344 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231075356311 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12344 0.011
      (momentAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12344 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12344
/-! The actual computed-centre upper energy formula at 12344. -/
namespace BstLean.Part264b.N12344
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12344

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12344
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12344 cell12344)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086606446377
  | 2 => 0.087571580704
  | 3 => 0.088538412888
  | 4 => 0.089509156979
  | 5 => 0.090486460578
  | 6 => 0.091473465149
  | 7 => 0.092473871279
  | 8 => 0.093492008801
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12344 12344 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12344 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12344

/-! Actual upper energy certificates on all 43 source endpoints at 12344. -/
namespace BstLean.Part264b.N12344
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12344 cell12344)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12344 (gMinus 12344) (1 - (cell12344 i).lower) ≤ 1 ∧
    energyUpper 12344 (gMinus 12344) (BstLean.Part211.gPlus 12344)
      (finiteEnergy 12344 12344 0.011) (1 - (cell12344 i).lower) ≤
      (cell12344 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12344) (by norm_num)
        (q := 1 - (cell12344 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12344,cell12344]) (by norm_num [scalarRow12344,cell12344])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12344,cell12344])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12344

/-! Source-cell containment and simple scalar guards at 12344. -/
namespace BstLean.Part264b.N12344
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12344 cell12344)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12344 ⟨10,by decide⟩).lower ∧ (cell12344 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12344 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12344 ⟨11,by decide⟩).lower ∧ (cell12344 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12344 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12344 ⟨12,by decide⟩).lower ∧ (cell12344 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12344 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12344 ⟨13,by decide⟩).lower ∧ (cell12344 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12344 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12344 ⟨14,by decide⟩).lower ∧ (cell12344 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12344 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12344 ⟨15,by decide⟩).lower ∧ (cell12344 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12344 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12344 ⟨16,by decide⟩).lower ∧ (cell12344 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12344 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12344 ⟨17,by decide⟩).lower ∧ (cell12344 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12344 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12344 ⟨18,by decide⟩).lower ∧ (cell12344 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12344 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12344 ⟨19,by decide⟩).lower ∧ (cell12344 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12344 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12344 ⟨20,by decide⟩).lower ∧ (cell12344 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12344 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12344 ⟨21,by decide⟩).lower ∧ (cell12344 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12344 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12344 ⟨22,by decide⟩).lower ∧ (cell12344 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12344 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12344 ⟨23,by decide⟩).lower ∧ (cell12344 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12344 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12344 ⟨24,by decide⟩).lower ∧ (cell12344 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12344 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12344 ⟨25,by decide⟩).lower ∧ (cell12344 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12344 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12344 ⟨26,by decide⟩).lower ∧ (cell12344 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12344 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12344 ⟨27,by decide⟩).lower ∧ (cell12344 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12344 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12344 ⟨28,by decide⟩).lower ∧ (cell12344 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12344 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12344 ⟨29,by decide⟩).lower ∧ (cell12344 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12344 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12344 ⟨30,by decide⟩).lower ∧ (cell12344 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12344 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12344 ⟨31,by decide⟩).lower ∧ (cell12344 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12344 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12344 ⟨32,by decide⟩).lower ∧ (cell12344 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12344 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12344 ⟨33,by decide⟩).lower ∧ (cell12344 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12344 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12344 ⟨34,by decide⟩).lower ∧ (cell12344 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12344 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12344 ⟨35,by decide⟩).lower ∧ (cell12344 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12344 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12344 ⟨36,by decide⟩).lower ∧ (cell12344 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12344 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12344 ⟨37,by decide⟩).lower ∧ (cell12344 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12344 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12344 ⟨38,by decide⟩).lower ∧ (cell12344 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12344 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12344 ⟨39,by decide⟩).lower ∧ (cell12344 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12344 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12344 ⟨40,by decide⟩).lower ∧ (cell12344 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12344 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12344 ⟨41,by decide⟩).lower ∧ (cell12344 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12344 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12344 ⟨42,by decide⟩).lower ∧ (cell12344 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12344 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12344 ⟨43,by decide⟩).lower ∧ (cell12344 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12344 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12344 ⟨44,by decide⟩).lower ∧ (cell12344 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12344 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12344 ⟨45,by decide⟩).lower ∧ (cell12344 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12344 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12344 ⟨46,by decide⟩).lower ∧ (cell12344 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12344 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12344 ⟨47,by decide⟩).lower ∧ (cell12344 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12344 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12344 ⟨48,by decide⟩).lower ∧ (cell12344 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12344 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12344 ⟨49,by decide⟩).lower ∧ (cell12344 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12344 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12344 ⟨50,by decide⟩).lower ∧ (cell12344 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12344 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12344 ⟨51,by decide⟩).lower ∧ (cell12344 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12344 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12344 ⟨52,by decide⟩).lower ∧ (cell12344 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12344 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12344 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12344 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12344,cell12344,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12344 i).lower ∧
    (cell12344 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12344 i).upper ≤ (0.532 : ℝ) ∧
    (cell12344 i).centre ≤ (0.1 : ℝ) ∧ (cell12344 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12344 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12344 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12344

/-! The local source numeric instances at 12344 have no network premises. -/
namespace BstLean.Part264b.N12344
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12344 cell12344)

noncomputable def sourceNumerics12344 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12344 (cell12344 i)
      scalarRow12344.M scalarRow12344.H scalarRow12344.xi := by
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
    energy_allowance := scalarRow12344.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12344]
    centre_nonneg := (scalarRow12344.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12344]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12344
/-! Actual 12345 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12345
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12345 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12345 12345 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12345.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12345 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12345 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12345 := gPlus_lower 12345
end BstLean.Part264b.N12345

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12345
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036325007861 : ℝ) ≤ wn 12345 := by
  have hn : √(12345 : ℝ) ≤ 111.108055513541 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12345 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.108055513541 ≤ 2 / √12345 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259253134 : ℝ) ≤ rhoBar 12345 BstLean.Part154.csC ∧
    rhoBar 12345 BstLean.Part154.csC ≤ 0.000259298563 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036325007861 : ℝ) / (1.295212 * 12345) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12345) := by gcongr
      _ ≤ (0.000259298563 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12345 BstLean.Part154.csC) ≤ 0.001037261488 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12345 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12345 BstLean.Part154.csC) (piBar (rhoBar 12345 BstLean.Part154.csC)) ≤ 0.000198054263 ∧
    cc1 (rhoBar 12345 BstLean.Part154.csC) (piBar (rhoBar 12345 BstLean.Part154.csC)) ≤ 0.000126023187 ∧
    cc2 (rhoBar 12345 BstLean.Part154.csC) ≤ 0.000073157358 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12345 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12345 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12345 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12345 BstLean.Part154.csC * nuR (rhoBar 12345 BstLean.Part154.csC)) ≤ 0.000518613935 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259298563 : ℝ) * 0.001037261488 := by gcongr
      _ ≤ (0.000518613935 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12345 BstLean.Part154.csC) * nuR (rhoBar 12345 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037261488 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12345 BstLean.Part154.csC) * rhoBar 12345 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259298563 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259298563 / 2 + 0.399 * 0.001037261488 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198054263 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518613935 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126023187 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259298563 / 1.414213562 := by gcongr
      _ ≤ (0.000073157358 : ℝ) := by norm_num

end BstLean.Part264b.N12345

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12345
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12345 BstLean.Part154.csC) (piBar (rhoBar 12345 BstLean.Part154.csC)) ≤ 1.69396E-7 := by
  have hr0 : 0 ≤ rhoBar 12345 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12345 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12345 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12345 BstLean.Part154.csC) (piBar (rhoBar 12345 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12345 BstLean.Part154.csC) (piBar (rhoBar 12345 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12345 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198054263 : ℝ) ^ 2 + 0.000126023187 ^ 2 + 3 * 0.000073157358 ^ 2 +
        2 * 0.797885 * 0.000198054263 * 0.000126023187 + 2 * 0.000198054263 * 0.000073157358 +
        4 * 0.797885 * 0.000126023187 * 0.000073157358 := by gcongr
    _ ≤ (1.69396E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12345 BstLean.Part154.csC Θ ≤ 0.002709009504 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12345 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12345 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12345 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12345 BstLean.Part154.csC) (piBar (rhoBar 12345 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12345 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69396E-7 / (0.000259253134 : ℝ) := by gcongr
    _ ≤ 0.002709009504 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12345 BstLean.Part154.csC Θ ≤ 0.003007288317 + 0.000684402703 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12345 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12345 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12345 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259298563 +
        (6863 / 10000) * 0.000259298563 * 12345 * 0.001037261488) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003007288317 + 0.000684402703 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12345 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12345 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12345 0.011 Θ ∧ gammaRatio 12345 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12345 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12345) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12345 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12345 0.011 Θ) :=
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
    badAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12345 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12345 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12345 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12345 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12345 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12345 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12345 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12345 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12345 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12345 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12345 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004107288317 + 0.003393412207 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12345

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12345
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12345 BstLean.Part154.csC) (piBar (rhoBar 12345 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12345 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12345 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12345 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12345 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12345 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12345 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12345 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12345 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12345 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12345 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12345 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12345 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053241839813 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12345) ≤ 0.010748433816 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12345 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010748433816 + 2 * 0.737676 / 12345) := by gcongr
    _ ≤ (0.053241839813 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12345 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12345

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12345
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487052474 : ℝ) ≤ plow 12345 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12345) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395429726)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422229990) : eMP 12345 0.011 xi bn ≤ 0.001223630178 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12345 : ℝ) * (1 - 0.011))) ≤ 0.000604945407 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001422229990 / (12345 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604945407 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604945407 : ℝ) + 3.141593 * 0.053395429726 / (12345 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001223630178 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395429726)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422229990) : PiBarMP 12345 12 0.011 xi bn ≤ 0.163588347938 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12345 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037712464651 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.495271392037 : ℝ) ≤ √((12345 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.108055513540 : ℝ) ≤ √12345 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12345) ≤ 0.125395122779 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037712464651 + 0.053395429726 * 1.772454 / (2 * (110.495271392037 : ℝ))) * (1 + 0.001223630178) +
        8 / (12345 * 111.108055513540) + 0.125395122779 := by gcongr
    _ ≤ (0.163588347938 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395429726)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422229990) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284316351013) :
    parallelOracle 12345 0.011 xi bn cd ≤ 0.164610807941 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12345 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12345 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487052474 : ℝ) ≤ plow 12345 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.108055513540 : ℝ) ≤ √12345 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284316351013 : ℝ) / (2 * 0.560487052474 * 111.108055513540)) * 0.163588347938 +
        0.284316351013 ^ 2 / (2 * 0.560487052474 * 111.108055513540) := by gcongr
    _ ≤ (0.164610807941 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395429726) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422229990)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284316351013) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12345 12345 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487052474 : ℝ) ≤ plow 12345 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.108055513540 : ℝ) ≤ √12345 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12345 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12345 Θ 1.22 ≤ 0.011935232724 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.108055513540 := by gcongr <;> linarith
      _ ≤ (0.011935232724 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12345 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12345 12345 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12345 12345 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12345 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12345 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12345 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12345 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164610807941 + 0.011935232724 + (0.008646 : ℝ) *
        (1 + 2 * (0.284316351013 + 0.011935232724) / (0.560487052474 * 111.108055513540))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12345]

end BstLean.Part264b.N12345

/-! The original eight local profiles supply actual 12345 moment certificates. -/
namespace BstLean.Part264b.N12345
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12345 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053395429726 ∧
    0 ≤ bN 12345 BstLean.Part154.csC (groupTheta g) ∧ bN 12345 BstLean.Part154.csC (groupTheta g) ≤ 0.001422229990 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12345 12345 0.011
      (momentAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12345 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12345 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12345 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231074511200 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12345 0.011
      (momentAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12345 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12345
/-! The actual computed-centre upper energy formula at 12345. -/
namespace BstLean.Part264b.N12345
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12345

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12345
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12345 cell12345)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086603063365
  | 2 => 0.087568123986
  | 3 => 0.088534869944
  | 4 => 0.089505512555
  | 5 => 0.090482696232
  | 6 => 0.091469558745
  | 7 => 0.092469796423
  | 8 => 0.093487734225
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12345 12345 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12345 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12345

/-! Actual upper energy certificates on all 43 source endpoints at 12345. -/
namespace BstLean.Part264b.N12345
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12345 cell12345)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12345 (gMinus 12345) (1 - (cell12345 i).lower) ≤ 1 ∧
    energyUpper 12345 (gMinus 12345) (BstLean.Part211.gPlus 12345)
      (finiteEnergy 12345 12345 0.011) (1 - (cell12345 i).lower) ≤
      (cell12345 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12345) (by norm_num)
        (q := 1 - (cell12345 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12345,cell12345]) (by norm_num [scalarRow12345,cell12345])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12345,cell12345])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12345

/-! Source-cell containment and simple scalar guards at 12345. -/
namespace BstLean.Part264b.N12345
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12345 cell12345)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12345 ⟨10,by decide⟩).lower ∧ (cell12345 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12345 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12345 ⟨11,by decide⟩).lower ∧ (cell12345 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12345 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12345 ⟨12,by decide⟩).lower ∧ (cell12345 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12345 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12345 ⟨13,by decide⟩).lower ∧ (cell12345 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12345 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12345 ⟨14,by decide⟩).lower ∧ (cell12345 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12345 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12345 ⟨15,by decide⟩).lower ∧ (cell12345 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12345 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12345 ⟨16,by decide⟩).lower ∧ (cell12345 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12345 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12345 ⟨17,by decide⟩).lower ∧ (cell12345 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12345 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12345 ⟨18,by decide⟩).lower ∧ (cell12345 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12345 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12345 ⟨19,by decide⟩).lower ∧ (cell12345 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12345 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12345 ⟨20,by decide⟩).lower ∧ (cell12345 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12345 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12345 ⟨21,by decide⟩).lower ∧ (cell12345 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12345 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12345 ⟨22,by decide⟩).lower ∧ (cell12345 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12345 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12345 ⟨23,by decide⟩).lower ∧ (cell12345 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12345 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12345 ⟨24,by decide⟩).lower ∧ (cell12345 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12345 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12345 ⟨25,by decide⟩).lower ∧ (cell12345 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12345 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12345 ⟨26,by decide⟩).lower ∧ (cell12345 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12345 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12345 ⟨27,by decide⟩).lower ∧ (cell12345 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12345 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12345 ⟨28,by decide⟩).lower ∧ (cell12345 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12345 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12345 ⟨29,by decide⟩).lower ∧ (cell12345 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12345 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12345 ⟨30,by decide⟩).lower ∧ (cell12345 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12345 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12345 ⟨31,by decide⟩).lower ∧ (cell12345 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12345 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12345 ⟨32,by decide⟩).lower ∧ (cell12345 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12345 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12345 ⟨33,by decide⟩).lower ∧ (cell12345 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12345 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12345 ⟨34,by decide⟩).lower ∧ (cell12345 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12345 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12345 ⟨35,by decide⟩).lower ∧ (cell12345 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12345 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12345 ⟨36,by decide⟩).lower ∧ (cell12345 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12345 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12345 ⟨37,by decide⟩).lower ∧ (cell12345 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12345 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12345 ⟨38,by decide⟩).lower ∧ (cell12345 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12345 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12345 ⟨39,by decide⟩).lower ∧ (cell12345 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12345 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12345 ⟨40,by decide⟩).lower ∧ (cell12345 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12345 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12345 ⟨41,by decide⟩).lower ∧ (cell12345 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12345 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12345 ⟨42,by decide⟩).lower ∧ (cell12345 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12345 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12345 ⟨43,by decide⟩).lower ∧ (cell12345 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12345 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12345 ⟨44,by decide⟩).lower ∧ (cell12345 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12345 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12345 ⟨45,by decide⟩).lower ∧ (cell12345 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12345 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12345 ⟨46,by decide⟩).lower ∧ (cell12345 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12345 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12345 ⟨47,by decide⟩).lower ∧ (cell12345 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12345 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12345 ⟨48,by decide⟩).lower ∧ (cell12345 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12345 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12345 ⟨49,by decide⟩).lower ∧ (cell12345 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12345 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12345 ⟨50,by decide⟩).lower ∧ (cell12345 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12345 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12345 ⟨51,by decide⟩).lower ∧ (cell12345 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12345 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12345 ⟨52,by decide⟩).lower ∧ (cell12345 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12345 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12345 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12345 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12345,cell12345,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12345 i).lower ∧
    (cell12345 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12345 i).upper ≤ (0.532 : ℝ) ∧
    (cell12345 i).centre ≤ (0.1 : ℝ) ∧ (cell12345 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12345 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12345 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12345

/-! The local source numeric instances at 12345 have no network premises. -/
namespace BstLean.Part264b.N12345
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12345 cell12345)

noncomputable def sourceNumerics12345 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12345 (cell12345 i)
      scalarRow12345.M scalarRow12345.H scalarRow12345.xi := by
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
    energy_allowance := scalarRow12345.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12345]
    centre_nonneg := (scalarRow12345.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12345]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12345
/-! Actual 12346 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12346
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12346 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12346 12346 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12346.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12346 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12346 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12346 := gPlus_lower 12346
end BstLean.Part264b.N12346

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12346
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036323523585 : ℝ) ≤ wn 12346 := by
  have hn : √(12346 : ℝ) ≤ 111.112555546167 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12346 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.112555546167 ≤ 2 / √12346 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259231764 : ℝ) ≤ rhoBar 12346 BstLean.Part154.csC ∧
    rhoBar 12346 BstLean.Part154.csC ≤ 0.000259277561 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036323523585 : ℝ) / (1.295212 * 12346) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12346) := by gcongr
      _ ≤ (0.000259277561 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12346 BstLean.Part154.csC) ≤ 0.001037177469 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12346 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12346 BstLean.Part154.csC) (piBar (rhoBar 12346 BstLean.Part154.csC)) ≤ 0.000198038221 ∧
    cc1 (rhoBar 12346 BstLean.Part154.csC) (piBar (rhoBar 12346 BstLean.Part154.csC)) ≤ 0.000126012979 ∧
    cc2 (rhoBar 12346 BstLean.Part154.csC) ≤ 0.000073151432 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12346 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12346 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12346 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12346 BstLean.Part154.csC * nuR (rhoBar 12346 BstLean.Part154.csC)) ≤ 0.000518571928 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259277561 : ℝ) * 0.001037177469 := by gcongr
      _ ≤ (0.000518571928 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12346 BstLean.Part154.csC) * nuR (rhoBar 12346 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037177469 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12346 BstLean.Part154.csC) * rhoBar 12346 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259277561 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259277561 / 2 + 0.399 * 0.001037177469 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198038221 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518571928 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126012979 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259277561 / 1.414213562 := by gcongr
      _ ≤ (0.000073151432 : ℝ) := by norm_num

end BstLean.Part264b.N12346

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12346
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12346 BstLean.Part154.csC) (piBar (rhoBar 12346 BstLean.Part154.csC)) ≤ 1.69369E-7 := by
  have hr0 : 0 ≤ rhoBar 12346 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12346 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12346 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12346 BstLean.Part154.csC) (piBar (rhoBar 12346 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12346 BstLean.Part154.csC) (piBar (rhoBar 12346 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12346 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198038221 : ℝ) ^ 2 + 0.000126012979 ^ 2 + 3 * 0.000073151432 ^ 2 +
        2 * 0.797885 * 0.000198038221 * 0.000126012979 + 2 * 0.000198038221 * 0.000073151432 +
        4 * 0.797885 * 0.000126012979 * 0.000073151432 := by gcongr
    _ ≤ (1.69369E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12346 BstLean.Part154.csC Θ ≤ 0.002708801000 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12346 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12346 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12346 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12346 BstLean.Part154.csC) (piBar (rhoBar 12346 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12346 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69369E-7 / (0.000259231764 : ℝ) := by gcongr
    _ ≤ 0.002708801000 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12346 BstLean.Part154.csC Θ ≤ 0.003007044732 + 0.000684347270 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12346 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12346 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12346 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259277561 +
        (6863 / 10000) * 0.000259277561 * 12346 * 0.001037177469) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003007044732 + 0.000684347270 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12346 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12346 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12346 0.011 Θ ∧ gammaRatio 12346 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12346 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12346) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12346 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12346 0.011 Θ) :=
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
    badAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12346 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12346 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12346 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12346 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12346 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12346 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12346 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12346 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12346 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12346 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12346 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004107044732 + 0.003393148270 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12346

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12346
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12346 BstLean.Part154.csC) (piBar (rhoBar 12346 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12346 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12346 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12346 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12346 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12346 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12346 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12346 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12346 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12346 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12346 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12346 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12346 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053239659820 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12346) ≤ 0.010747998507 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12346 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010747998507 + 2 * 0.737676 / 12346) := by gcongr
    _ ≤ (0.053239659820 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12346 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12346

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12346
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487100332 : ℝ) ≤ plow 12346 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12346) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395047574)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422120525) : eMP 12346 0.011 xi bn ≤ 0.001223533407 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12346 : ℝ) * (1 - 0.011))) ≤ 0.000604897627 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001422120525 / (12346 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604897627 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604897627 : ℝ) + 3.141593 * 0.053395047574 / (12346 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001223533407 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395047574)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422120525) : PiBarMP 12346 12 0.011 xi bn ≤ 0.163581791516 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12346 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037711013312 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.499746606044 : ℝ) ≤ √((12346 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.112555546166 : ℝ) ≤ √12346 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12346) ≤ 0.125390044305 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037711013312 + 0.053395047574 * 1.772454 / (2 * (110.499746606044 : ℝ))) * (1 + 0.001223533407) +
        8 / (12346 * 111.112555546166) + 0.125390044305 := by gcongr
    _ ≤ (0.163581791516 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395047574)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422120525) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284313344116) :
    parallelOracle 12346 0.011 xi bn cd ≤ 0.164604177380 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12346 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12346 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487100332 : ℝ) ≤ plow 12346 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.112555546166 : ℝ) ≤ √12346 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284313344116 : ℝ) / (2 * 0.560487100332 * 111.112555546166)) * 0.163581791516 +
        0.284313344116 ^ 2 / (2 * 0.560487100332 * 111.112555546166) := by gcongr
    _ ≤ (0.164604177380 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053395047574) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422120525)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284313344116) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12346 12346 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487100332 : ℝ) ≤ plow 12346 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.112555546166 : ℝ) ≤ √12346 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12346 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12346 Θ 1.22 ≤ 0.011934749350 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.112555546166 := by gcongr <;> linarith
      _ ≤ (0.011934749350 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12346 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12346 12346 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12346 12346 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12346 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12346 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12346 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12346 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164604177380 + 0.011934749350 + (0.008646 : ℝ) *
        (1 + 2 * (0.284313344116 + 0.011934749350) / (0.560487100332 * 111.112555546166))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12346]

end BstLean.Part264b.N12346

/-! The original eight local profiles supply actual 12346 moment certificates. -/
namespace BstLean.Part264b.N12346
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12346 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053395047574 ∧
    0 ≤ bN 12346 BstLean.Part154.csC (groupTheta g) ∧ bN 12346 BstLean.Part154.csC (groupTheta g) ≤ 0.001422120525 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12346 12346 0.011
      (momentAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12346 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12346 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12346 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231073684296 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12346 0.011
      (momentAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12346 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12346
/-! The actual computed-centre upper energy formula at 12346. -/
namespace BstLean.Part264b.N12346
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12346

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12346
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12346 cell12346)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086599681931
  | 2 => 0.087564668918
  | 3 => 0.088531328736
  | 4 => 0.089501869974
  | 5 => 0.090478933861
  | 6 => 0.091465654473
  | 7 => 0.092465723888
  | 8 => 0.093483462196
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12346 12346 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12346 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12346

/-! Actual upper energy certificates on all 43 source endpoints at 12346. -/
namespace BstLean.Part264b.N12346
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12346 cell12346)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12346 (gMinus 12346) (1 - (cell12346 i).lower) ≤ 1 ∧
    energyUpper 12346 (gMinus 12346) (BstLean.Part211.gPlus 12346)
      (finiteEnergy 12346 12346 0.011) (1 - (cell12346 i).lower) ≤
      (cell12346 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12346) (by norm_num)
        (q := 1 - (cell12346 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12346,cell12346]) (by norm_num [scalarRow12346,cell12346])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12346,cell12346])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12346

/-! Source-cell containment and simple scalar guards at 12346. -/
namespace BstLean.Part264b.N12346
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12346 cell12346)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12346 ⟨10,by decide⟩).lower ∧ (cell12346 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12346 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12346 ⟨11,by decide⟩).lower ∧ (cell12346 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12346 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12346 ⟨12,by decide⟩).lower ∧ (cell12346 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12346 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12346 ⟨13,by decide⟩).lower ∧ (cell12346 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12346 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12346 ⟨14,by decide⟩).lower ∧ (cell12346 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12346 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12346 ⟨15,by decide⟩).lower ∧ (cell12346 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12346 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12346 ⟨16,by decide⟩).lower ∧ (cell12346 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12346 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12346 ⟨17,by decide⟩).lower ∧ (cell12346 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12346 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12346 ⟨18,by decide⟩).lower ∧ (cell12346 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12346 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12346 ⟨19,by decide⟩).lower ∧ (cell12346 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12346 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12346 ⟨20,by decide⟩).lower ∧ (cell12346 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12346 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12346 ⟨21,by decide⟩).lower ∧ (cell12346 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12346 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12346 ⟨22,by decide⟩).lower ∧ (cell12346 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12346 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12346 ⟨23,by decide⟩).lower ∧ (cell12346 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12346 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12346 ⟨24,by decide⟩).lower ∧ (cell12346 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12346 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12346 ⟨25,by decide⟩).lower ∧ (cell12346 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12346 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12346 ⟨26,by decide⟩).lower ∧ (cell12346 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12346 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12346 ⟨27,by decide⟩).lower ∧ (cell12346 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12346 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12346 ⟨28,by decide⟩).lower ∧ (cell12346 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12346 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12346 ⟨29,by decide⟩).lower ∧ (cell12346 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12346 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12346 ⟨30,by decide⟩).lower ∧ (cell12346 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12346 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12346 ⟨31,by decide⟩).lower ∧ (cell12346 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12346 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12346 ⟨32,by decide⟩).lower ∧ (cell12346 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12346 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12346 ⟨33,by decide⟩).lower ∧ (cell12346 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12346 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12346 ⟨34,by decide⟩).lower ∧ (cell12346 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12346 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12346 ⟨35,by decide⟩).lower ∧ (cell12346 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12346 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12346 ⟨36,by decide⟩).lower ∧ (cell12346 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12346 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12346 ⟨37,by decide⟩).lower ∧ (cell12346 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12346 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12346 ⟨38,by decide⟩).lower ∧ (cell12346 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12346 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12346 ⟨39,by decide⟩).lower ∧ (cell12346 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12346 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12346 ⟨40,by decide⟩).lower ∧ (cell12346 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12346 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12346 ⟨41,by decide⟩).lower ∧ (cell12346 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12346 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12346 ⟨42,by decide⟩).lower ∧ (cell12346 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12346 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12346 ⟨43,by decide⟩).lower ∧ (cell12346 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12346 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12346 ⟨44,by decide⟩).lower ∧ (cell12346 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12346 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12346 ⟨45,by decide⟩).lower ∧ (cell12346 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12346 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12346 ⟨46,by decide⟩).lower ∧ (cell12346 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12346 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12346 ⟨47,by decide⟩).lower ∧ (cell12346 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12346 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12346 ⟨48,by decide⟩).lower ∧ (cell12346 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12346 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12346 ⟨49,by decide⟩).lower ∧ (cell12346 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12346 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12346 ⟨50,by decide⟩).lower ∧ (cell12346 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12346 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12346 ⟨51,by decide⟩).lower ∧ (cell12346 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12346 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12346 ⟨52,by decide⟩).lower ∧ (cell12346 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12346 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12346 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12346 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12346,cell12346,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12346 i).lower ∧
    (cell12346 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12346 i).upper ≤ (0.532 : ℝ) ∧
    (cell12346 i).centre ≤ (0.1 : ℝ) ∧ (cell12346 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12346 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12346 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12346

/-! The local source numeric instances at 12346 have no network premises. -/
namespace BstLean.Part264b.N12346
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12346 cell12346)

noncomputable def sourceNumerics12346 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12346 (cell12346 i)
      scalarRow12346.M scalarRow12346.H scalarRow12346.xi := by
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
    energy_allowance := scalarRow12346.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12346]
    centre_nonneg := (scalarRow12346.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12346]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12346
/-! Actual 12347 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12347
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12347 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12347 12347 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12347.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12347 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12347 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12347 := gPlus_lower 12347
end BstLean.Part264b.N12347

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12347
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036322039490 : ℝ) ≤ wn 12347 := by
  have hn : √(12347 : ℝ) ≤ 111.117055396551 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12347 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.117055396551 ≤ 2 / √12347 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259210397 : ℝ) ≤ rhoBar 12347 BstLean.Part154.csC ∧
    rhoBar 12347 BstLean.Part154.csC ≤ 0.000259256561 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036322039490 : ℝ) / (1.295212 * 12347) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12347) := by gcongr
      _ ≤ (0.000259256561 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12347 BstLean.Part154.csC) ≤ 0.001037093458 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12347 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12347 BstLean.Part154.csC) (piBar (rhoBar 12347 BstLean.Part154.csC)) ≤ 0.000198022180 ∧
    cc1 (rhoBar 12347 BstLean.Part154.csC) (piBar (rhoBar 12347 BstLean.Part154.csC)) ≤ 0.000126002773 ∧
    cc2 (rhoBar 12347 BstLean.Part154.csC) ≤ 0.000073145507 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12347 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12347 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12347 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12347 BstLean.Part154.csC * nuR (rhoBar 12347 BstLean.Part154.csC)) ≤ 0.000518529926 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259256561 : ℝ) * 0.001037093458 := by gcongr
      _ ≤ (0.000518529926 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12347 BstLean.Part154.csC) * nuR (rhoBar 12347 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037093458 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12347 BstLean.Part154.csC) * rhoBar 12347 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259256561 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259256561 / 2 + 0.399 * 0.001037093458 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198022180 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518529926 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000126002773 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259256561 / 1.414213562 := by gcongr
      _ ≤ (0.000073145507 : ℝ) := by norm_num

end BstLean.Part264b.N12347

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12347
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12347 BstLean.Part154.csC) (piBar (rhoBar 12347 BstLean.Part154.csC)) ≤ 1.69341E-7 := by
  have hr0 : 0 ≤ rhoBar 12347 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12347 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12347 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12347 BstLean.Part154.csC) (piBar (rhoBar 12347 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12347 BstLean.Part154.csC) (piBar (rhoBar 12347 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12347 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198022180 : ℝ) ^ 2 + 0.000126002773 ^ 2 + 3 * 0.000073145507 ^ 2 +
        2 * 0.797885 * 0.000198022180 * 0.000126002773 + 2 * 0.000198022180 * 0.000073145507 +
        4 * 0.797885 * 0.000126002773 * 0.000073145507 := by gcongr
    _ ≤ (1.69341E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12347 BstLean.Part154.csC Θ ≤ 0.002708576435 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12347 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12347 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12347 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12347 BstLean.Part154.csC) (piBar (rhoBar 12347 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12347 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69341E-7 / (0.000259210397 : ℝ) := by gcongr
    _ ≤ 0.002708576435 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12347 BstLean.Part154.csC Θ ≤ 0.003006801153 + 0.000684291842 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12347 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12347 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12347 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259256561 +
        (6863 / 10000) * 0.000259256561 * 12347 * 0.001037093458) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003006801153 + 0.000684291842 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12347 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12347 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12347 0.011 Θ ∧ gammaRatio 12347 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12347 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12347) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12347 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12347 0.011 Θ) :=
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
    badAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12347 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12347 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12347 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12347 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12347 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12347 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12347 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12347 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12347 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12347 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12347 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004106801153 + 0.003392868277 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12347

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12347
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12347 BstLean.Part154.csC) (piBar (rhoBar 12347 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12347 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12347 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12347 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12347 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12347 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12347 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12347 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12347 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12347 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12347 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12347 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12347 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053237480095 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12347) ≤ 0.010747563251 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12347 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010747563251 + 2 * 0.737676 / 12347) := by gcongr
    _ ≤ (0.053237480095 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12347 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12347

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12347
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487148181 : ℝ) ≤ plow 12347 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12347) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053394656999)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422002629) : eMP 12347 0.011 xi bn ≤ 0.001223433056 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12347 : ℝ) * (1 - 0.011))) ≤ 0.000604848058 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001422002629 / (12347 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604848058 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604848058 : ℝ) + 3.141593 * 0.053394656999 / (12347 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001223433056 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053394656999)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422002629) : PiBarMP 12347 12 0.011 xi bn ≤ 0.163575123529 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12347 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037709450129 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.504221638813 : ℝ) ≤ √((12347 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.117055396550 : ℝ) ≤ √12347 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12347) ≤ 0.125384966449 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037709450129 + 0.053394656999 * 1.772454 / (2 * (110.504221638813 : ℝ))) * (1 + 0.001223433056) +
        8 / (12347 * 111.117055396550) + 0.125384966449 := by gcongr
    _ ≤ (0.163575123529 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053394656999)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422002629) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284310319259) :
    parallelOracle 12347 0.011 xi bn cd ≤ 0.164597434901 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12347 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12347 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487148181 : ℝ) ≤ plow 12347 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.117055396550 : ℝ) ≤ √12347 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284310319259 : ℝ) / (2 * 0.560487148181 * 111.117055396550)) * 0.163575123529 +
        0.284310319259 ^ 2 / (2 * 0.560487148181 * 111.117055396550) := by gcongr
    _ ≤ (0.164597434901 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053394656999) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001422002629)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284310319259) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12347 12347 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487148181 : ℝ) ≤ plow 12347 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.117055396550 : ℝ) ≤ √12347 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12347 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12347 Θ 1.22 ≤ 0.011934266034 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.117055396550 := by gcongr <;> linarith
      _ ≤ (0.011934266034 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12347 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12347 12347 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12347 12347 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12347 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12347 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12347 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12347 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164597434901 + 0.011934266034 + (0.008646 : ℝ) *
        (1 + 2 * (0.284310319259 + 0.011934266034) / (0.560487148181 * 111.117055396550))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12347]

end BstLean.Part264b.N12347

/-! The original eight local profiles supply actual 12347 moment certificates. -/
namespace BstLean.Part264b.N12347
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12347 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053394656999 ∧
    0 ≤ bN 12347 BstLean.Part154.csC (groupTheta g) ∧ bN 12347 BstLean.Part154.csC (groupTheta g) ≤ 0.001422002629 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12347 12347 0.011
      (momentAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12347 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12347 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12347 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231072839164 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12347 0.011
      (momentAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12347 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12347
/-! The actual computed-centre upper energy formula at 12347. -/
namespace BstLean.Part264b.N12347
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12347

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12347
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12347 cell12347)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086596302075
  | 2 => 0.087561215497
  | 3 => 0.088527789264
  | 4 => 0.089498229236
  | 5 => 0.090475173461
  | 6 => 0.091461752330
  | 7 => 0.092461653671
  | 8 => 0.093479192712
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12347 12347 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12347 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12347

/-! Actual upper energy certificates on all 43 source endpoints at 12347. -/
namespace BstLean.Part264b.N12347
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12347 cell12347)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12347 (gMinus 12347) (1 - (cell12347 i).lower) ≤ 1 ∧
    energyUpper 12347 (gMinus 12347) (BstLean.Part211.gPlus 12347)
      (finiteEnergy 12347 12347 0.011) (1 - (cell12347 i).lower) ≤
      (cell12347 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12347) (by norm_num)
        (q := 1 - (cell12347 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12347,cell12347]) (by norm_num [scalarRow12347,cell12347])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12347,cell12347])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12347

/-! Source-cell containment and simple scalar guards at 12347. -/
namespace BstLean.Part264b.N12347
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12347 cell12347)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12347 ⟨10,by decide⟩).lower ∧ (cell12347 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12347 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12347 ⟨11,by decide⟩).lower ∧ (cell12347 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12347 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12347 ⟨12,by decide⟩).lower ∧ (cell12347 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12347 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12347 ⟨13,by decide⟩).lower ∧ (cell12347 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12347 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12347 ⟨14,by decide⟩).lower ∧ (cell12347 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12347 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12347 ⟨15,by decide⟩).lower ∧ (cell12347 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12347 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12347 ⟨16,by decide⟩).lower ∧ (cell12347 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12347 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12347 ⟨17,by decide⟩).lower ∧ (cell12347 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12347 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12347 ⟨18,by decide⟩).lower ∧ (cell12347 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12347 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12347 ⟨19,by decide⟩).lower ∧ (cell12347 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12347 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12347 ⟨20,by decide⟩).lower ∧ (cell12347 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12347 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12347 ⟨21,by decide⟩).lower ∧ (cell12347 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12347 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12347 ⟨22,by decide⟩).lower ∧ (cell12347 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12347 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12347 ⟨23,by decide⟩).lower ∧ (cell12347 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12347 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12347 ⟨24,by decide⟩).lower ∧ (cell12347 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12347 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12347 ⟨25,by decide⟩).lower ∧ (cell12347 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12347 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12347 ⟨26,by decide⟩).lower ∧ (cell12347 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12347 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12347 ⟨27,by decide⟩).lower ∧ (cell12347 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12347 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12347 ⟨28,by decide⟩).lower ∧ (cell12347 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12347 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12347 ⟨29,by decide⟩).lower ∧ (cell12347 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12347 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12347 ⟨30,by decide⟩).lower ∧ (cell12347 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12347 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12347 ⟨31,by decide⟩).lower ∧ (cell12347 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12347 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12347 ⟨32,by decide⟩).lower ∧ (cell12347 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12347 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12347 ⟨33,by decide⟩).lower ∧ (cell12347 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12347 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12347 ⟨34,by decide⟩).lower ∧ (cell12347 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12347 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12347 ⟨35,by decide⟩).lower ∧ (cell12347 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12347 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12347 ⟨36,by decide⟩).lower ∧ (cell12347 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12347 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12347 ⟨37,by decide⟩).lower ∧ (cell12347 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12347 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12347 ⟨38,by decide⟩).lower ∧ (cell12347 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12347 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12347 ⟨39,by decide⟩).lower ∧ (cell12347 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12347 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12347 ⟨40,by decide⟩).lower ∧ (cell12347 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12347 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12347 ⟨41,by decide⟩).lower ∧ (cell12347 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12347 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12347 ⟨42,by decide⟩).lower ∧ (cell12347 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12347 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12347 ⟨43,by decide⟩).lower ∧ (cell12347 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12347 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12347 ⟨44,by decide⟩).lower ∧ (cell12347 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12347 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12347 ⟨45,by decide⟩).lower ∧ (cell12347 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12347 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12347 ⟨46,by decide⟩).lower ∧ (cell12347 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12347 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12347 ⟨47,by decide⟩).lower ∧ (cell12347 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12347 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12347 ⟨48,by decide⟩).lower ∧ (cell12347 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12347 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12347 ⟨49,by decide⟩).lower ∧ (cell12347 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12347 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12347 ⟨50,by decide⟩).lower ∧ (cell12347 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12347 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12347 ⟨51,by decide⟩).lower ∧ (cell12347 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12347 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12347 ⟨52,by decide⟩).lower ∧ (cell12347 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12347 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12347 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12347 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12347,cell12347,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12347 i).lower ∧
    (cell12347 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12347 i).upper ≤ (0.532 : ℝ) ∧
    (cell12347 i).centre ≤ (0.1 : ℝ) ∧ (cell12347 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12347 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12347 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12347

/-! The local source numeric instances at 12347 have no network premises. -/
namespace BstLean.Part264b.N12347
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12347 cell12347)

noncomputable def sourceNumerics12347 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12347 (cell12347 i)
      scalarRow12347.M scalarRow12347.H scalarRow12347.xi := by
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
    energy_allowance := scalarRow12347.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12347]
    centre_nonneg := (scalarRow12347.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12347]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12347
/-! Actual 12348 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12348
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12348 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12348 12348 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12348.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12348 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12348 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12348 := gPlus_lower 12348
end BstLean.Part264b.N12348

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12348
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036320555576 : ℝ) ≤ wn 12348 := by
  have hn : √(12348 : ℝ) ≤ 111.121555064713 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12348 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.121555064713 ≤ 2 / √12348 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259189034 : ℝ) ≤ rhoBar 12348 BstLean.Part154.csC ∧
    rhoBar 12348 BstLean.Part154.csC ≤ 0.000259235566 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036320555576 : ℝ) / (1.295212 * 12348) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12348) := by gcongr
      _ ≤ (0.000259235566 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12348 BstLean.Part154.csC) ≤ 0.001037009468 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12348 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12348 BstLean.Part154.csC) (piBar (rhoBar 12348 BstLean.Part154.csC)) ≤ 0.000198006143 ∧
    cc1 (rhoBar 12348 BstLean.Part154.csC) (piBar (rhoBar 12348 BstLean.Part154.csC)) ≤ 0.000125992568 ∧
    cc2 (rhoBar 12348 BstLean.Part154.csC) ≤ 0.000073139584 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12348 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12348 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12348 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12348 BstLean.Part154.csC * nuR (rhoBar 12348 BstLean.Part154.csC)) ≤ 0.000518487933 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259235566 : ℝ) * 0.001037009468 := by gcongr
      _ ≤ (0.000518487933 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12348 BstLean.Part154.csC) * nuR (rhoBar 12348 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001037009468 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12348 BstLean.Part154.csC) * rhoBar 12348 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259235566 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259235566 / 2 + 0.399 * 0.001037009468 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000198006143 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518487933 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125992568 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259235566 / 1.414213562 := by gcongr
      _ ≤ (0.000073139584 : ℝ) := by norm_num

end BstLean.Part264b.N12348

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12348
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12348 BstLean.Part154.csC) (piBar (rhoBar 12348 BstLean.Part154.csC)) ≤ 1.69314E-7 := by
  have hr0 : 0 ≤ rhoBar 12348 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12348 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12348 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12348 BstLean.Part154.csC) (piBar (rhoBar 12348 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12348 BstLean.Part154.csC) (piBar (rhoBar 12348 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12348 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000198006143 : ℝ) ^ 2 + 0.000125992568 ^ 2 + 3 * 0.000073139584 ^ 2 +
        2 * 0.797885 * 0.000198006143 * 0.000125992568 + 2 * 0.000198006143 * 0.000073139584 +
        4 * 0.797885 * 0.000125992568 * 0.000073139584 := by gcongr
    _ ≤ (1.69314E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12348 BstLean.Part154.csC Θ ≤ 0.002708367787 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12348 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12348 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12348 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12348 BstLean.Part154.csC) (piBar (rhoBar 12348 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12348 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69314E-7 / (0.000259189034 : ℝ) := by gcongr
    _ ≤ 0.002708367787 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12348 BstLean.Part154.csC Θ ≤ 0.003006557654 + 0.000684236427 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12348 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12348 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12348 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259235566 +
        (6863 / 10000) * 0.000259235566 * 12348 * 0.001037009468) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003006557654 + 0.000684236427 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12348 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12348 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12348 0.011 Θ ∧ gammaRatio 12348 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12348 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12348) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12348 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12348 0.011 Θ) :=
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
    badAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12348 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12348 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12348 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12348 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12348 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12348 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12348 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12348 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12348 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12348 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12348 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004106557654 + 0.003392604214 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12348

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12348
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12348 BstLean.Part154.csC) (piBar (rhoBar 12348 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12348 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12348 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12348 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12348 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12348 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12348 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12348 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12348 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12348 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12348 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12348 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12348 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053235300632 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12348) ≤ 0.010747128047 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12348 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010747128047 + 2 * 0.737676 / 12348) := by gcongr
    _ ≤ (0.053235300632 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12348 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12348

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12348
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487196023 : ℝ) ≤ plow 12348 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12348) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053394274867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421893089) : eMP 12348 0.011 xi bn ≤ 0.001223336269 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12348 : ℝ) * (1 - 0.011))) ≤ 0.000604800270 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001421893089 / (12348 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604800270 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604800270 : ℝ) + 3.141593 * 0.053394274867 / (12348 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001223336269 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053394274867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421893089) : PiBarMP 12348 12 0.011 xi bn ≤ 0.163568567235 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12348 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037707997680 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.508696490366 : ℝ) ≤ √((12348 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.121555064712 : ℝ) ≤ √12348 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12348) ≤ 0.125379889210 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037707997680 + 0.053394274867 * 1.772454 / (2 * (110.508696490366 : ℝ))) * (1 + 0.001223336269) +
        8 / (12348 * 111.121555064712) + 0.125379889210 := by gcongr
    _ ≤ (0.163568567235 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053394274867)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421893089) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284307312930) :
    parallelOracle 12348 0.011 xi bn cd ≤ 0.164590804488 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12348 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12348 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487196023 : ℝ) ≤ plow 12348 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.121555064712 : ℝ) ≤ √12348 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284307312930 : ℝ) / (2 * 0.560487196023 * 111.121555064712)) * 0.163568567235 +
        0.284307312930 ^ 2 / (2 * 0.560487196023 * 111.121555064712) := by gcongr
    _ ≤ (0.164590804488 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053394274867) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421893089)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284307312930) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12348 12348 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487196023 : ℝ) ≤ plow 12348 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.121555064712 : ℝ) ≤ √12348 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12348 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12348 Θ 1.22 ≤ 0.011933782778 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.121555064712 := by gcongr <;> linarith
      _ ≤ (0.011933782778 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12348 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12348 12348 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12348 12348 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12348 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12348 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12348 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12348 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164590804488 + 0.011933782778 + (0.008646 : ℝ) *
        (1 + 2 * (0.284307312930 + 0.011933782778) / (0.560487196023 * 111.121555064712))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12348]

end BstLean.Part264b.N12348

/-! The original eight local profiles supply actual 12348 moment certificates. -/
namespace BstLean.Part264b.N12348
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12348 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053394274867 ∧
    0 ≤ bN 12348 BstLean.Part154.csC (groupTheta g) ∧ bN 12348 BstLean.Part154.csC (groupTheta g) ≤ 0.001421893089 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12348 12348 0.011
      (momentAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12348 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12348 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12348 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231072012298 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12348 0.011
      (momentAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12348 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12348
/-! The actual computed-centre upper energy formula at 12348. -/
namespace BstLean.Part264b.N12348
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12348

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12348
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12348 cell12348)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086592923794
  | 2 => 0.087557763723
  | 3 => 0.088524251524
  | 4 => 0.089494590337
  | 5 => 0.090471415031
  | 6 => 0.091457852313
  | 7 => 0.092457585770
  | 8 => 0.093474925771
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12348 12348 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12348 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12348

/-! Actual upper energy certificates on all 43 source endpoints at 12348. -/
namespace BstLean.Part264b.N12348
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12348 cell12348)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12348 (gMinus 12348) (1 - (cell12348 i).lower) ≤ 1 ∧
    energyUpper 12348 (gMinus 12348) (BstLean.Part211.gPlus 12348)
      (finiteEnergy 12348 12348 0.011) (1 - (cell12348 i).lower) ≤
      (cell12348 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12348) (by norm_num)
        (q := 1 - (cell12348 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12348,cell12348]) (by norm_num [scalarRow12348,cell12348])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12348,cell12348])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12348

/-! Source-cell containment and simple scalar guards at 12348. -/
namespace BstLean.Part264b.N12348
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12348 cell12348)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12348 ⟨10,by decide⟩).lower ∧ (cell12348 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12348 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12348 ⟨11,by decide⟩).lower ∧ (cell12348 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12348 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12348 ⟨12,by decide⟩).lower ∧ (cell12348 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12348 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12348 ⟨13,by decide⟩).lower ∧ (cell12348 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12348 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12348 ⟨14,by decide⟩).lower ∧ (cell12348 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12348 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12348 ⟨15,by decide⟩).lower ∧ (cell12348 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12348 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12348 ⟨16,by decide⟩).lower ∧ (cell12348 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12348 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12348 ⟨17,by decide⟩).lower ∧ (cell12348 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12348 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12348 ⟨18,by decide⟩).lower ∧ (cell12348 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12348 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12348 ⟨19,by decide⟩).lower ∧ (cell12348 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12348 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12348 ⟨20,by decide⟩).lower ∧ (cell12348 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12348 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12348 ⟨21,by decide⟩).lower ∧ (cell12348 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12348 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12348 ⟨22,by decide⟩).lower ∧ (cell12348 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12348 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12348 ⟨23,by decide⟩).lower ∧ (cell12348 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12348 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12348 ⟨24,by decide⟩).lower ∧ (cell12348 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12348 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12348 ⟨25,by decide⟩).lower ∧ (cell12348 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12348 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12348 ⟨26,by decide⟩).lower ∧ (cell12348 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12348 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12348 ⟨27,by decide⟩).lower ∧ (cell12348 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12348 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12348 ⟨28,by decide⟩).lower ∧ (cell12348 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12348 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12348 ⟨29,by decide⟩).lower ∧ (cell12348 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12348 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12348 ⟨30,by decide⟩).lower ∧ (cell12348 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12348 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12348 ⟨31,by decide⟩).lower ∧ (cell12348 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12348 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12348 ⟨32,by decide⟩).lower ∧ (cell12348 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12348 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12348 ⟨33,by decide⟩).lower ∧ (cell12348 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12348 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12348 ⟨34,by decide⟩).lower ∧ (cell12348 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12348 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12348 ⟨35,by decide⟩).lower ∧ (cell12348 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12348 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12348 ⟨36,by decide⟩).lower ∧ (cell12348 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12348 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12348 ⟨37,by decide⟩).lower ∧ (cell12348 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12348 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12348 ⟨38,by decide⟩).lower ∧ (cell12348 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12348 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12348 ⟨39,by decide⟩).lower ∧ (cell12348 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12348 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12348 ⟨40,by decide⟩).lower ∧ (cell12348 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12348 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12348 ⟨41,by decide⟩).lower ∧ (cell12348 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12348 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12348 ⟨42,by decide⟩).lower ∧ (cell12348 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12348 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12348 ⟨43,by decide⟩).lower ∧ (cell12348 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12348 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12348 ⟨44,by decide⟩).lower ∧ (cell12348 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12348 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12348 ⟨45,by decide⟩).lower ∧ (cell12348 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12348 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12348 ⟨46,by decide⟩).lower ∧ (cell12348 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12348 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12348 ⟨47,by decide⟩).lower ∧ (cell12348 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12348 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12348 ⟨48,by decide⟩).lower ∧ (cell12348 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12348 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12348 ⟨49,by decide⟩).lower ∧ (cell12348 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12348 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12348 ⟨50,by decide⟩).lower ∧ (cell12348 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12348 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12348 ⟨51,by decide⟩).lower ∧ (cell12348 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12348 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12348 ⟨52,by decide⟩).lower ∧ (cell12348 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12348 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12348 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12348 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12348,cell12348,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12348 i).lower ∧
    (cell12348 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12348 i).upper ≤ (0.532 : ℝ) ∧
    (cell12348 i).centre ≤ (0.1 : ℝ) ∧ (cell12348 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12348 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12348 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12348

/-! The local source numeric instances at 12348 have no network premises. -/
namespace BstLean.Part264b.N12348
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12348 cell12348)

noncomputable def sourceNumerics12348 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12348 (cell12348 i)
      scalarRow12348.M scalarRow12348.H scalarRow12348.xi := by
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
    energy_allowance := scalarRow12348.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12348]
    centre_nonneg := (scalarRow12348.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12348]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12348
/-! Actual 12349 scalar aliases and the unchanged imported parallel allowance. -/

namespace BstLean.Part264b.N12349
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12349 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12349 12349 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part263.scalarRow12349.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12349 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12349 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12349 := gPlus_lower 12349
end BstLean.Part264b.N12349

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part264b.N12349
open BstLean.Part253 BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036319071844 : ℝ) ≤ wn 12349 := by
  have hn : √(12349 : ℝ) ≤ 111.126054550677 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12349 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.126054550677 ≤ 2 / √12349 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000259167674 : ℝ) ≤ rhoBar 12349 BstLean.Part154.csC ∧
    rhoBar 12349 BstLean.Part154.csC ≤ 0.000259214573 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036319071844 : ℝ) / (1.295212 * 12349) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12349) := by gcongr
      _ ≤ (0.000259214573 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12349 BstLean.Part154.csC) ≤ 0.001036925485 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12349 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12349 BstLean.Part154.csC) (piBar (rhoBar 12349 BstLean.Part154.csC)) ≤ 0.000197990108 ∧
    cc1 (rhoBar 12349 BstLean.Part154.csC) (piBar (rhoBar 12349 BstLean.Part154.csC)) ≤ 0.000125982365 ∧
    cc2 (rhoBar 12349 BstLean.Part154.csC) ≤ 0.000073133661 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12349 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12349 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12349 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12349 BstLean.Part154.csC * nuR (rhoBar 12349 BstLean.Part154.csC)) ≤ 0.000518445944 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259214573 : ℝ) * 0.001036925485 := by gcongr
      _ ≤ (0.000518445944 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12349 BstLean.Part154.csC) * nuR (rhoBar 12349 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001036925485 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12349 BstLean.Part154.csC) * rhoBar 12349 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259214573 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259214573 / 2 + 0.399 * 0.001036925485 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197990108 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518445944 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125982365 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259214573 / 1.414213562 := by gcongr
      _ ≤ (0.000073133661 : ℝ) := by norm_num

end BstLean.Part264b.N12349

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part264b.N12349
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12349 BstLean.Part154.csC) (piBar (rhoBar 12349 BstLean.Part154.csC)) ≤ 1.69286E-7 := by
  have hr0 : 0 ≤ rhoBar 12349 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12349 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12349 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12349 BstLean.Part154.csC) (piBar (rhoBar 12349 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12349 BstLean.Part154.csC) (piBar (rhoBar 12349 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12349 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197990108 : ℝ) ^ 2 + 0.000125982365 ^ 2 + 3 * 0.000073133661 ^ 2 +
        2 * 0.797885 * 0.000197990108 * 0.000125982365 + 2 * 0.000197990108 * 0.000073133661 +
        4 * 0.797885 * 0.000125982365 * 0.000073133661 := by gcongr
    _ ≤ (1.69286E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12349 BstLean.Part154.csC Θ ≤ 0.002708143076 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12349 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12349 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12349 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12349 BstLean.Part154.csC) (piBar (rhoBar 12349 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12349 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69286E-7 / (0.000259167674 : ℝ) := by gcongr
    _ ≤ 0.002708143076 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12349 BstLean.Part154.csC Θ ≤ 0.003006314159 + 0.000684181017 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12349 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12349 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12349 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259214573 +
        (6863 / 10000) * 0.000259214573 * 12349 * 0.001036925485) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003006314159 + 0.000684181017 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12349 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12349 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12349 0.011 Θ ∧ gammaRatio 12349 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12349 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12349) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12349 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12349 0.011 Θ) :=
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
    badAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12349 BstLean.Part154.csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12349 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12349 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12349 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12349 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12349 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12349 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12349 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12349 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12349 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12349 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004106314159 + 0.003392324093 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part264b.N12349

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264b.N12349
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12349 BstLean.Part154.csC) (piBar (rhoBar 12349 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12349 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12349 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12349 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12349 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12349 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12349 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12349 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12349 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12349 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12349 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12349 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12349 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.053233121442 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12349) ≤ 0.010746692897 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12349 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010746692897 + 2 * 0.737676 / 12349) := by gcongr
    _ ≤ (0.053233121442 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12349 12 ≤ 0.0015 := by
  exact BstLean.Part264b.uniform_n22_upper (by norm_num)

end BstLean.Part264b.N12349

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part264b.N12349
open BstLean.Part253 BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487243857 : ℝ) ≤ plow 12349 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12349) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053393884308)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421775115) : eMP 12349 0.011 xi bn ≤ 0.001223235900 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12349 : ℝ) * (1 - 0.011))) ≤ 0.000604750692 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001421775115 / (12349 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604750692 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604750692 : ℝ) + 3.141593 * 0.053393884308 / (12349 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001223235900 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053393884308)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421775115) : PiBarMP 12349 12 0.011 xi bn ≤ 0.163561899326 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12349 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037706433338 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.513171160726 : ℝ) ≤ √((12349 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.126054550676 : ℝ) ≤ √12349 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12349) ≤ 0.125374812587 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037706433338 + 0.053393884308 * 1.772454 / (2 * (110.513171160726 : ℝ))) * (1 + 0.001223235900) +
        8 / (12349 * 111.126054550676) + 0.125374812587 := by gcongr
    _ ≤ (0.163561899326 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053393884308)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421775115) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284304288636) :
    parallelOracle 12349 0.011 xi bn cd ≤ 0.164584062107 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12349 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12349 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487243857 : ℝ) ≤ plow 12349 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.126054550676 : ℝ) ≤ √12349 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284304288636 : ℝ) / (2 * 0.560487243857 * 111.126054550676)) * 0.163561899326 +
        0.284304288636 ^ 2 / (2 * 0.560487243857 * 111.126054550676) := by gcongr
    _ ≤ (0.164584062107 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053393884308) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421775115)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284304288636) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12349 12349 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487243857 : ℝ) ≤ plow 12349 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.126054550676 : ℝ) ≤ √12349 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12349 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12349 Θ 1.22 ≤ 0.011933299580 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.126054550676 := by gcongr <;> linarith
      _ ≤ (0.011933299580 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12349 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12349 12349 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12349 12349 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12349 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12349 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12349 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12349 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164584062107 + 0.011933299580 + (0.008646 : ℝ) *
        (1 + 2 * (0.284304288636 + 0.011933299580) / (0.560487243857 * 111.126054550676))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part263.scalarRow12349]

end BstLean.Part264b.N12349

/-! The original eight local profiles supply actual 12349 moment certificates. -/
namespace BstLean.Part264b.N12349
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12349 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053393884308 ∧
    0 ≤ bN 12349 BstLean.Part154.csC (groupTheta g) ∧ bN 12349 BstLean.Part154.csC (groupTheta g) ≤ 0.001421775115 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12349 12349 0.011
      (momentAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12349 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12349 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12349 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231071167194 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12349 0.011
      (momentAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12349 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part264b.N12349
/-! The actual computed-centre upper energy formula at 12349. -/
namespace BstLean.Part264b.N12349
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part264b.N12349

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part264b.N12349
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12349 cell12349)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086589547087
  | 2 => 0.087554313593
  | 3 => 0.088520715516
  | 4 => 0.089490953275
  | 5 => 0.090467658568
  | 6 => 0.091453954421
  | 7 => 0.092453520182
  | 8 => 0.093470661368
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12349 12349 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12349 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part264b.N12349

/-! Actual upper energy certificates on all 43 source endpoints at 12349. -/
namespace BstLean.Part264b.N12349
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part263 (scalarRow12349 cell12349)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12349 (gMinus 12349) (1 - (cell12349 i).lower) ≤ 1 ∧
    energyUpper 12349 (gMinus 12349) (BstLean.Part211.gPlus 12349)
      (finiteEnergy 12349 12349 0.011) (1 - (cell12349 i).lower) ≤
      (cell12349 i).energy := by
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
      have E := BstLean.Part264b.uniformEnergy10 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨10,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy11 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨11,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy12 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨12,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy13 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨13,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy14 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨14,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy15 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨15,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy16 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨16,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy17 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨17,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy18 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨18,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy19 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨19,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy20 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨20,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy21 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨21,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy22 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨22,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy23 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨23,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy24 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨24,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy25 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨25,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy26 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨26,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy27 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨27,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy28 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨28,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy29 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨29,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy30 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨30,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy31 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨31,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy32 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨32,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy33 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨33,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy34 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨34,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy35 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨35,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy36 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨36,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy37 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨37,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy38 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨38,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy39 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨39,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy40 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨40,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy41 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨41,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy42 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨42,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy43 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨43,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy44 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨44,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy45 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨45,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy46 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨46,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy47 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨47,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy48 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨48,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy49 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨49,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy50 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨50,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy51 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨51,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part264b.uniformEnergy52 (n := 12349) (by norm_num)
        (q := 1 - (cell12349 ⟨52,by decide⟩).lower)
        (by norm_num [scalarRow12349,cell12349]) (by norm_num [scalarRow12349,cell12349])
      exact ⟨E.1,E.2.trans (by norm_num [scalarRow12349,cell12349])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part264b.N12349

/-! Source-cell containment and simple scalar guards at 12349. -/
namespace BstLean.Part264b.N12349
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12349 cell12349)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12349 ⟨10,by decide⟩).lower ∧ (cell12349 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12349 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12349 ⟨11,by decide⟩).lower ∧ (cell12349 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12349 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12349 ⟨12,by decide⟩).lower ∧ (cell12349 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12349 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12349 ⟨13,by decide⟩).lower ∧ (cell12349 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12349 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12349 ⟨14,by decide⟩).lower ∧ (cell12349 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12349 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12349 ⟨15,by decide⟩).lower ∧ (cell12349 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12349 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12349 ⟨16,by decide⟩).lower ∧ (cell12349 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12349 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12349 ⟨17,by decide⟩).lower ∧ (cell12349 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12349 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12349 ⟨18,by decide⟩).lower ∧ (cell12349 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12349 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12349 ⟨19,by decide⟩).lower ∧ (cell12349 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12349 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12349 ⟨20,by decide⟩).lower ∧ (cell12349 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12349 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12349 ⟨21,by decide⟩).lower ∧ (cell12349 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12349 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12349 ⟨22,by decide⟩).lower ∧ (cell12349 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12349 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12349 ⟨23,by decide⟩).lower ∧ (cell12349 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12349 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12349 ⟨24,by decide⟩).lower ∧ (cell12349 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12349 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12349 ⟨25,by decide⟩).lower ∧ (cell12349 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12349 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12349 ⟨26,by decide⟩).lower ∧ (cell12349 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12349 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12349 ⟨27,by decide⟩).lower ∧ (cell12349 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12349 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12349 ⟨28,by decide⟩).lower ∧ (cell12349 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12349 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12349 ⟨29,by decide⟩).lower ∧ (cell12349 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12349 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12349 ⟨30,by decide⟩).lower ∧ (cell12349 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12349 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12349 ⟨31,by decide⟩).lower ∧ (cell12349 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12349 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12349 ⟨32,by decide⟩).lower ∧ (cell12349 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12349 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12349 ⟨33,by decide⟩).lower ∧ (cell12349 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12349 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12349 ⟨34,by decide⟩).lower ∧ (cell12349 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12349 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12349 ⟨35,by decide⟩).lower ∧ (cell12349 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12349 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12349 ⟨36,by decide⟩).lower ∧ (cell12349 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12349 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12349 ⟨37,by decide⟩).lower ∧ (cell12349 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12349 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12349 ⟨38,by decide⟩).lower ∧ (cell12349 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12349 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12349 ⟨39,by decide⟩).lower ∧ (cell12349 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12349 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12349 ⟨40,by decide⟩).lower ∧ (cell12349 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12349 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12349 ⟨41,by decide⟩).lower ∧ (cell12349 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12349 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12349 ⟨42,by decide⟩).lower ∧ (cell12349 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12349 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12349 ⟨43,by decide⟩).lower ∧ (cell12349 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12349 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12349 ⟨44,by decide⟩).lower ∧ (cell12349 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12349 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12349 ⟨45,by decide⟩).lower ∧ (cell12349 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12349 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12349 ⟨46,by decide⟩).lower ∧ (cell12349 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12349 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12349 ⟨47,by decide⟩).lower ∧ (cell12349 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12349 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12349 ⟨48,by decide⟩).lower ∧ (cell12349 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12349 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12349 ⟨49,by decide⟩).lower ∧ (cell12349 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12349 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12349 ⟨50,by decide⟩).lower ∧ (cell12349 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12349 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12349 ⟨51,by decide⟩).lower ∧ (cell12349 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12349 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12349 ⟨52,by decide⟩).lower ∧ (cell12349 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12349 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12349 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12349 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12349,cell12349,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12349 i).lower ∧
    (cell12349 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12349 i).upper ≤ (0.532 : ℝ) ∧
    (cell12349 i).centre ≤ (0.1 : ℝ) ∧ (cell12349 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12349 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12349 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part264b.N12349

/-! The local source numeric instances at 12349 have no network premises. -/
namespace BstLean.Part264b.N12349
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part263 (scalarRow12349 cell12349)

noncomputable def sourceNumerics12349 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    CellSourceNumerics 12349 (cell12349 i)
      scalarRow12349.M scalarRow12349.H scalarRow12349.xi := by
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
    energy_allowance := scalarRow12349.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12349]
    centre_nonneg := (scalarRow12349.certificate i).centre_nonneg
    centre_upper := hc
    direction_allowance := by norm_num [scalarRow12349]
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part264b.N12349
