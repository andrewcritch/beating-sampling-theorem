import BstLean.Part269Source
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
import BstLean.Part264bSourceCommon
import BstLean.Part269Row12350
/-! Actual 12350 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12350
open BstLean.Part264
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12350 ≤ (1.036505 : ℝ) := wn_upper (by norm_num)
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12350 12350 (11 / 1000) ≤
    (0.008646 : ℝ) := finite_centre_upper (by norm_num)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12350.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12350 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12350 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12350 := gPlus_lower 12350
end BstLean.Part269.N12350

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12350
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036317588292 : ℝ) ≤ wn 12350 := by
  have hn : √(12350 : ℝ) ≤ 111.130553854465 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12350 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.130553854465 ≤ 2 / √12350 := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_cs_upper : csC ≤ 1.295212 := by
  have hp := pi_lt_d6.le
  have hd : (1 : ℝ) / 3.141593 ≤ 1 / π := by gcongr
  unfold csC
  linarith

theorem pilot_rho_bounds : (0.000259146318 : ℝ) ≤ rhoBar 12350 csC ∧
    rhoBar 12350 csC ≤ 0.000259193584 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := pilot_cs_upper
  have hc0 : 0 < csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036317588292 : ℝ) / (1.295212 * 12350) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036505 : ℝ) / (1.29521 * 12350) := by gcongr
      _ ≤ (0.000259193584 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12350 csC) ≤ 0.001036841518 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12350 csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12350 csC) :=
    le_sqrt_of_sq_le (by linarith)
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √2 ≤ 0.707106782 := by
    calc
      _ ≤ (1 : ℝ) / 1.414213562 := by gcongr
      _ ≤ (0.707106782 : ℝ) := by norm_num
  have hgap : (0.292631318 : ℝ) ≤ √(1 - 2 * rhoBar 12350 csC) - 1 / √2 := by linarith
  have hexp : (100 : ℝ) ≤ (√(1 - 2 * rhoBar 12350 csC) - 1 / √2) ^ 2 /
      (2 * rhoBar 12350 csC) := by
    apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12350 csC)).mpr
    nlinarith
  have h := exp_negative_bound 100 (by norm_num : ((2.71828 : ℝ) ^ 100)⁻¹ ≤ 1 / 10 ^ 40)
  unfold piBar
  apply le_trans ?_ h
  apply exp_le_exp.mpr
  norm_num only [Nat.cast_ofNat]
  linarith

theorem pilot_phi_zero_upper : phiG 0 ≤ 0.399 := by
  have hs : (2.506628 : ℝ) ≤ √(2 * π) := le_sqrt_of_sq_le (by linarith [pi_gt_d6])
  unfold phiG
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, neg_zero, exp_zero, mul_one]
  have h := (inv_le_inv₀ (by positivity : 0 < √(2 * π)) (by norm_num : (0 : ℝ) < 2.506628)).mpr hs
  exact h.trans (by norm_num)

theorem pilot_phi_one_upper : phiG 1 ≤ 0.243 := by
  have hz := pilot_phi_zero_upper
  have he := exp_half_lower
  have he' : exp (-(1 / 2 : ℝ)) ≤ (1.6487 : ℝ)⁻¹ := by
    rw [exp_neg]
    exact (inv_le_inv₀ (exp_pos _) (by norm_num)).mpr he
  have hid : phiG 1 = phiG 0 * exp (-(1 / 2 : ℝ)) := by
    unfold phiG
    norm_num
  rw [hid]
  calc
    _ ≤ (0.399 : ℝ) * (1.6487 : ℝ)⁻¹ :=
      mul_le_mul hz he' (exp_pos _).le (by norm_num)
    _ ≤ (0.243 : ℝ) := by norm_num

theorem pilot_cc_bounds : cc0 (rhoBar 12350 csC) (piBar (rhoBar 12350 csC)) ≤ 0.000197974075 ∧
    cc1 (rhoBar 12350 csC) (piBar (rhoBar 12350 csC)) ≤ 0.000125972164 ∧
    cc2 (rhoBar 12350 csC) ≤ 0.000073127739 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12350 csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12350 csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12350 csC) := by unfold piBar; positivity
  have hz := pilot_phi_zero_upper
  have ho := pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12350 csC * nuR (rhoBar 12350 csC)) ≤ 0.000518403964 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000259193584 : ℝ) * 0.001036841518 := by gcongr
      _ ≤ (0.000518403964 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12350 csC) * nuR (rhoBar 12350 csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001036841518 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12350 csC) * rhoBar 12350 csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000259193584 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000259193584 / 2 + 0.399 * 0.001036841518 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000197974075 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000518403964 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000125972164 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000259193584 / 1.414213562 := by gcongr
      _ ≤ (0.000073127739 : ℝ) := by norm_num

end BstLean.Part269.N12350

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12350
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12350 csC) (piBar (rhoBar 12350 csC)) ≤ 1.69259E-7 := by
  have hr0 : 0 ≤ rhoBar 12350 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12350 csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12350 csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12350 csC) (piBar (rhoBar 12350 csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12350 csC) (piBar (rhoBar 12350 csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12350 csC) := by unfold cc2; positivity
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
    _ ≤ (0.000197974075 : ℝ) ^ 2 + 0.000125972164 ^ 2 + 3 * 0.000073127739 ^ 2 +
        2 * 0.797885 * 0.000197974075 * 0.000125972164 + 2 * 0.000197974075 * 0.000073127739 +
        4 * 0.797885 * 0.000125972164 * 0.000073127739 := by gcongr
    _ ≤ (1.69259E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12350 csC Θ ≤ 0.002707934285 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12350 csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12350 csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12350 csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12350 csC) (piBar (rhoBar 12350 csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12350 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036505 * 1.69259E-7 / (0.000259146318 : ℝ) := by gcongr
    _ ≤ 0.002707934285 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12350 csC Θ ≤ 0.003006070718 + 0.000684125618 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12350 csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12350 csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12350 csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036505 : ℝ) * ((2 * Θ * 0.000259193584 +
        (6863 / 10000) * 0.000259193584 * 12350 * 0.001036841518) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003006070718 + 0.000684125618 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12350 csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12350 csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12350 0.011 Θ ∧ gammaRatio 12350 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12350 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036505 : ℝ) * 0.525 / ((1 - 0.011) * 12350) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12350 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12350 0.011 Θ) :=
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
    badAllowance 12350 csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12350 csC) 1.22 ≤ 0.0000000414 := by
    have he : (17 : ℝ) ≤ gap 2 (rhoBar 12350 csC) 1.22 ^ 2 / (2 * rhoBar 12350 csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12350 csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_seventeen_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12350 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12350 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12350 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12350 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12350 csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12350 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036505 : ℝ) * 12350 *
        (0.0000000414 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
    _ ≤ (0.0011 : ℝ) := by norm_num

theorem pilot_rest_upper {S : ℝ} (hS : 0 ≤ S) : restAllowance csC 0.011 1.22 1.12 S ≤ 0.2654 * S := by
  have hk : K0 ≤ 0.090846 := by
    unfold K0
    apply (div_le_iff₀ (by positivity : 0 < 4 * π)).mpr
    linarith [pi_lt_d6]
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hs : √((1.22 : ℝ) * 1.12) ≤ 1.169 := sqrt_le_iff.mpr (by norm_num)
  have hd : (1.6006 : ℝ) ≤ √(2 * csC * (1 - 0.011)) :=
    le_sqrt_of_sq_le (by linarith [cs_lower])
  unfold restAllowance
  calc
    _ ≤ 4 * (0.090846 : ℝ) * 1.169 * S / 1.6006 := by gcongr
    _ ≤ 0.2654 * S := by ring_nf; nlinarith only [hS]

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12350 csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004106070718 + 0.003392059903 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12350

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12350
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12350 csC) (piBar (rhoBar 12350 csC)) := by
  have hr0 : 0 ≤ rhoBar 12350 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12350 csC)
  have hv0 : 0 ≤ nuR (rhoBar 12350 csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12350 csC Θ := by
  have hr0 : 0 ≤ rhoBar 12350 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12350 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12350 csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12350 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12350 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12350 csC)
  have hv0 : 0 ≤ nuR (rhoBar 12350 csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12350 csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12350 csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12350 csC 0.011 0.46 Θ ≤ 0.053230942514 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / 12350) ≤ 0.010746257799 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12350 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010746257799 + 2 * 0.737676 / 12350) := by gcongr
    _ ≤ (0.053230942514 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12350 12 ≤ 0.0015 := by
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar 12350 12 ≤ 0.000749634 := by
    unfold N12bar
    simp only [Nat.cast_ofNat]
    linarith
  have h10 : 0 ≤ N12bar 12350 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem pilot_radial_centre_bound {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.130553854464 ≤ R) : xiNr 12350 Θ 1.22 ≤ R := by
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hn := pilot_n22_upper
  have hn0 : 0 ≤ N22bar 12350 12 := by unfold N22bar N12bar; positivity
  have hN : (111.130553854464 : ℝ) ≤ √12350 := le_sqrt_of_sq_le (by norm_num)
  unfold xiNr
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  gcongr
  linarith

theorem pilot_full_formula_bound {Θ S X T R B : ℝ}
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.004106070718 + 0.003392059903 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 111.130553854464 ≤ R)
    (hB : (X + 0.053230942514 + R + 0.008646) ^ 2 ≤ B) :
    fullFormula 12350 12350 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance 12350 csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, (pilot_moment_upper hw hS).trans hXsq⟩
  have hd := pilot_deviation_upper hΘ hw.2
  have hr := pilot_radial_centre_bound hΘ hT hTsq hR
  have hf : finiteEnergy 12350 12350 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation 12350 csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar 12350 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr 12350 Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg 12350 12350 (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

end BstLean.Part269.N12350

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12350
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560487291684 : ℝ) ≤ plow 12350 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12350) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053393502168)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421665500) : eMP 12350 0.011 xi bn ≤ 0.001223139098 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12350 : ℝ) * (1 - 0.011))) ≤ 0.000604702896 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001421665500 / (12350 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000604702896 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000604702896 : ℝ) + 3.141593 * 0.053393502168 / (12350 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001223139098 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053393502168)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421665500) : PiBarMP 12350 12 0.011 xi bn ≤ 0.163555343158 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12350 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037704979778 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (110.517645649914 : ℝ) ≤ √((12350 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.130553854464 : ℝ) ≤ √12350 := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12350) ≤ 0.125369736581 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037704979778 + 0.053393502168 * 1.772454 / (2 * (110.517645649914 : ℝ))) * (1 + 0.001223139098) +
        8 / (12350 * 111.130553854464) + 0.125369736581 := by gcongr
    _ ≤ (0.163555343158 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053393502168)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421665500) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284301282818) :
    parallelOracle 12350 0.011 xi bn cd ≤ 0.164577431840 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12350 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12350 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560487291684 : ℝ) ≤ plow 12350 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.130553854464 : ℝ) ≤ √12350 := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284301282818 : ℝ) / (2 * 0.560487291684 * 111.130553854464)) * 0.163555343158 +
        0.284301282818 ^ 2 / (2 * 0.560487291684 * 111.130553854464) := by gcongr
    _ ≤ (0.164577431840 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053393502168) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001421665500)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284301282818) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12350 12350 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560487291684 : ℝ) ≤ plow 12350 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.130553854464 : ℝ) ≤ √12350 := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12350 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12350 Θ 1.22 ≤ 0.011932816440 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.130553854464 := by gcongr <;> linarith
      _ ≤ (0.011932816440 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12350 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12350 12350 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12350 12350 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12350 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12350 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12350 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12350 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.164577431840 + 0.011932816440 + (0.008646 : ℝ) *
        (1 + 2 * (0.284301282818 + 0.011932816440) / (0.560487291684 * 111.130553854464))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12350]

end BstLean.Part269.N12350

/-! The original eight local profiles supply actual 12350 moment certificates. -/
namespace BstLean.Part269.N12350
open BstLean.Part264
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12350 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12350 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12350 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053393502168 ∧
    0 ≤ bN 12350 csC (groupTheta g) ∧ bN 12350 csC (groupTheta g) ≤ 0.001421665500 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12350 12350 0.011
      (momentAllowance 12350 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12350 csC (groupTheta g))
      (√(momentAllowance 12350 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12350 csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12350 csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12350 csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.231070340304 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12350 0.011
      (momentAllowance 12350 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12350 csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12350
/-! The actual computed-centre upper energy formula at 12350. -/
namespace BstLean.Part269.N12350
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem pilot_energy_upper_from_kappas {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12350 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12350 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12350 + 0.008646 / 111.130553854464) ^ 2 ≤ B) :
    energyRatio 12350 (gMinus 12350) q ≤ Q2 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 (11 / 1000)) q ≤ B := by
  have hs : √(kappa q + 5 / (12350 : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot 12350 q ≤ R := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hm0 : 0 ≤ meanRoot 12350 q := by unfold meanRoot; positivity
  have hR0 : 0 ≤ R := hm0.trans hm
  have hg := pilot_gMinus_lower
  have hg0 : 0 < gMinus 12350 := by linarith
  have hratio : energyRatio 12350 (gMinus 12350) q ≤ Q2 := by
    unfold energyRatio
    apply le_trans ?_ hQ2
    gcongr
  have hr0 : 0 ≤ energyRatio 12350 (gMinus 12350) q := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) hg0.le
  have hQ20 : 0 ≤ Q2 := hr0.trans hratio
  have hk := kappa_monotoneOn
    (show energyRatio 12350 (gMinus 12350) q ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show Q2 ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩) hratio
  have hk' := hk.trans hK2
  have hk0 := (kappa_mem (by linarith : -1 ≤ energyRatio 12350 (gMinus 12350) q)
    (by linarith : energyRatio 12350 (gMinus 12350) q ≤ 1)).1
  have hgp := pilot_gPlus_upper
  have hgp0 : 0 ≤ BstLean.Part211.gPlus 12350 := le_trans zero_le_one pilot_gPlus_lower
  have ht : √(BstLean.Part211.gPlus 12350 * kappa (energyRatio 12350 (gMinus 12350) q)) ≤ T := by
    apply sqrt_le_iff.mpr
    refine ⟨hT, ?_⟩
    exact (mul_le_mul hgp hk' hk0 (by norm_num)).trans hTsq
  have ht2 : √(12 * BstLean.Part211.gPlus 12350) ≤ 3.466066 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hn : (111.130553854464 : ℝ) ≤ √12350 := le_sqrt_of_sq_le (by norm_num)
  have hf := pilot_finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12350 12350 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hB
  gcongr


end BstLean.Part269.N12350

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12350
open BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12350)
open BstLean.Part268 (cell12350)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086586171952
  | 2 => 0.087550865105
  | 3 => 0.088517181237
  | 4 => 0.089487318049
  | 5 => 0.090463904070
  | 6 => 0.091450058650
  | 7 => 0.092449456904
  | 8 => 0.093466399501
  | _ => 0

theorem pilot_fullGroup1 :
    fullFormula 12350 12350 0.011 1.22 1.12 0.46 (groupTheta 1)
      (groupProfile 1) 1.22 ≤ pilotGroupCentre 1 := by
  apply pilot_full_formula_bound (X := (0.220639803866 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.011120861327 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup2 :
    fullFormula 12350 12350 0.011 1.22 1.12 0.46 (groupTheta 2)
      (groupProfile 2) 1.22 ≤ pilotGroupCentre 2 := by
  apply pilot_full_formula_bound (X := (0.222201701266 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.011237446321 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup3 :
    fullFormula 12350 12350 0.011 1.22 1.12 0.46 (groupTheta 3)
      (groupProfile 3) 1.22 ≤ pilotGroupCentre 3 := by
  apply pilot_full_formula_bound (X := (0.223743357533 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.011353646245 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup4 :
    fullFormula 12350 12350 0.011 1.22 1.12 0.46 (groupTheta 4)
      (groupProfile 4) 1.22 ≤ pilotGroupCentre 4 := by
  apply pilot_full_formula_bound (X := (0.225264972345 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011469469539 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup5 :
    fullFormula 12350 12350 0.011 1.22 1.12 0.46 (groupTheta 5)
      (groupProfile 5) 1.22 ≤ pilotGroupCentre 5 := by
  apply pilot_full_formula_bound (X := (0.226766740586 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011584924404 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup6 :
    fullFormula 12350 12350 0.011 1.22 1.12 0.46 (groupTheta 6)
      (groupProfile 6) 1.22 ≤ pilotGroupCentre 6 := by
  apply pilot_full_formula_bound (X := (0.228248850835 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011700018684 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup7 :
    fullFormula 12350 12350 0.011 1.22 1.12 0.46 (groupTheta 7)
      (groupProfile 7) 1.22 ≤ pilotGroupCentre 7 := by
  apply pilot_full_formula_bound (X := (0.229711487216 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011814760012 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup8 :
    fullFormula 12350 12350 0.011 1.22 1.12 0.46 (groupTheta 8)
      (groupProfile 8) 1.22 ≤ pilotGroupCentre 8 := by
  apply pilot_full_formula_bound (X := (0.231154827920 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011929155693 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12350 12350 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact pilot_fullGroup1
  | ⟨2,h⟩ => exact pilot_fullGroup2
  | ⟨3,h⟩ => exact pilot_fullGroup3
  | ⟨4,h⟩ => exact pilot_fullGroup4
  | ⟨5,h⟩ => exact pilot_fullGroup5
  | ⟨6,h⟩ => exact pilot_fullGroup6
  | ⟨7,h⟩ => exact pilot_fullGroup7
  | ⟨8,h⟩ => exact pilot_fullGroup8
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12350

/-! Actual upper energy certificates on all 43 source endpoints at 12350. -/
namespace BstLean.Part269.N12350
open BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12350)
open BstLean.Part268 (cell12350)
theorem pilot_upperEnergy10 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨10,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨10,by decide⟩).lower) ≤ (scalarRow12350.table ⟨10,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨10,by decide⟩).lower) ≤ 0.627908839638 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528019689447 : ℝ)) (s := (0.849232128194 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.629917151753 : ℝ) ≤ 0.699115368641 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629917151753 : ℝ)) (Q := (0.629917151753 : ℝ))
      (s := (0.776662334563 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨10,by decide⟩).lower)
    (U := (0.792662411080 : ℝ)) (R := (0.793223399259 : ℝ)) (Q2 := (0.629917151753 : ℝ)) (T := (0.836605051183 : ℝ))
    (B := (scalarRow12350.table ⟨10,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy11 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨11,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨11,by decide⟩).lower) ≤ (scalarRow12350.table ⟨11,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨11,by decide⟩).lower) ≤ 0.627096532092 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526821658392 : ℝ)) (s := (0.849975846863 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.629103346966 : ℝ) ≤ 0.698529476139 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629103346966 : ℝ)) (Q := (0.629103346966 : ℝ))
      (s := (0.777321670119 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨11,by decide⟩).lower)
    (U := (0.792149853495 : ℝ)) (R := (0.792710841674 : ℝ)) (Q2 := (0.629103346966 : ℝ)) (T := (0.836254419952 : ℝ))
    (B := (scalarRow12350.table ⟨11,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy12 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨12,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨12,by decide⟩).lower) ≤ (scalarRow12350.table ⟨12,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨12,by decide⟩).lower) ≤ 0.626284781758 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525623627337 : ℝ)) (s := (0.850717228217 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.628290100046 : ℝ) ≤ 0.697944272101 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628290100046 : ℝ)) (Q := (0.628290100046 : ℝ))
      (s := (0.777979145084 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨12,by decide⟩).lower)
    (U := (0.791637315984 : ℝ)) (R := (0.792198304163 : ℝ)) (Q2 := (0.628290100046 : ℝ)) (T := (0.835904053919 : ℝ))
    (B := (scalarRow12350.table ⟨12,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy13 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨13,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨13,by decide⟩).lower) ≤ (scalarRow12350.table ⟨13,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨13,by decide⟩).lower) ≤ 0.625473587968 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524425596282 : ℝ)) (s := (0.851456278364 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.627477410324 : ℝ) ≤ 0.697359755212 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627477410324 : ℝ)) (Q := (0.627477410324 : ℝ))
      (s := (0.778634766456 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨13,by decide⟩).lower)
    (U := (0.791124798163 : ℝ)) (R := (0.791685786342 : ℝ)) (Q2 := (0.627477410324 : ℝ)) (T := (0.835553952630 : ℝ))
    (B := (scalarRow12350.table ⟨13,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy14 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨14,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨14,by decide⟩).lower) ≤ (scalarRow12350.table ⟨14,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨14,by decide⟩).lower) ≤ 0.624662950054 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523227565226 : ℝ)) (s := (0.852193003368 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.626665277130 : ℝ) ≤ 0.696775924158 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626665277130 : ℝ)) (Q := (0.626665277130 : ℝ))
      (s := (0.779288541197 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨14,by decide⟩).lower)
    (U := (0.790612299648 : ℝ)) (R := (0.791173287827 : ℝ)) (Q2 := (0.626665277130 : ℝ)) (T := (0.835204115631 : ℝ))
    (B := (scalarRow12350.table ⟨14,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy15 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨15,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨15,by decide⟩).lower) ≤ (scalarRow12350.table ⟨15,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨15,by decide⟩).lower) ≤ 0.623852867357 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522029534171 : ℝ)) (s := (0.852927409252 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.625853699804 : ℝ) ≤ 0.696192777637 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625853699804 : ℝ)) (Q := (0.625853699804 : ℝ))
      (s := (0.779940476218 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨15,by decide⟩).lower)
    (U := (0.790099820059 : ℝ)) (R := (0.790660808238 : ℝ)) (Q2 := (0.625853699804 : ℝ)) (T := (0.834854542471 : ℝ))
    (B := (scalarRow12350.table ⟨15,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy16 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨16,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨16,by decide⟩).lower) ≤ (scalarRow12350.table ⟨16,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨16,by decide⟩).lower) ≤ 0.623043339217 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520831503116 : ℝ)) (s := (0.853659502005 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.625042677686 : ℝ) ≤ 0.695610314346 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625042677686 : ℝ)) (Q := (0.625042677686 : ℝ))
      (s := (0.780590578390 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨16,by decide⟩).lower)
    (U := (0.789587359016 : ℝ)) (R := (0.790148347195 : ℝ)) (Q2 := (0.625042677686 : ℝ)) (T := (0.834505232703 : ℝ))
    (B := (scalarRow12350.table ⟨16,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy17 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨17,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨17,by decide⟩).lower) ≤ (scalarRow12350.table ⟨17,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨17,by decide⟩).lower) ≤ 0.622234364977 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519633472060 : ℝ)) (s := (0.854389287571 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.624232210114 : ℝ) ≤ 0.695028532984 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624232210114 : ℝ)) (Q := (0.624232210114 : ℝ))
      (s := (0.781238854549 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨17,by decide⟩).lower)
    (U := (0.789074916137 : ℝ)) (R := (0.789635904316 : ℝ)) (Q2 := (0.624232210114 : ℝ)) (T := (0.834156185876 : ℝ))
    (B := (scalarRow12350.table ⟨17,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy18 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨18,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨18,by decide⟩).lower) ≤ (scalarRow12350.table ⟨18,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨18,by decide⟩).lower) ≤ 0.621425943984 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518435441005 : ℝ)) (s := (0.855116771857 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.623422296440 : ℝ) ≤ 0.694447432260 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623422296440 : ℝ)) (Q := (0.623422296440 : ℝ))
      (s := (0.781885311476 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨18,by decide⟩).lower)
    (U := (0.788562491046 : ℝ)) (R := (0.789123479225 : ℝ)) (Q2 := (0.623422296440 : ℝ)) (T := (0.833807401545 : ℝ))
    (B := (scalarRow12350.table ⟨18,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy19 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨19,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨19,by decide⟩).lower) ≤ (scalarRow12350.table ⟨19,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨19,by decide⟩).lower) ≤ 0.620618075588 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517237409950 : ℝ)) (s := (0.855841960732 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.622612936008 : ℝ) ≤ 0.693867010882 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622612936008 : ℝ)) (Q := (0.622612936008 : ℝ))
      (s := (0.782529955923 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨19,by decide⟩).lower)
    (U := (0.788050083363 : ℝ)) (R := (0.788611071542 : ℝ)) (Q2 := (0.622612936008 : ℝ)) (T := (0.833458879263 : ℝ))
    (B := (scalarRow12350.table ⟨19,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy20 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨20,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨20,by decide⟩).lower) ≤ (scalarRow12350.table ⟨20,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨20,by decide⟩).lower) ≤ 0.619810759143 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516039378894 : ℝ)) (s := (0.856564860026 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.621804128172 : ℝ) ≤ 0.693287267564 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621804128172 : ℝ)) (Q := (0.621804128172 : ℝ))
      (s := (0.783172794592 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨20,by decide⟩).lower)
    (U := (0.787537692713 : ℝ)) (R := (0.788098680892 : ℝ)) (Q2 := (0.621804128172 : ℝ)) (T := (0.833110618587 : ℝ))
    (B := (scalarRow12350.table ⟨20,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy21 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨21,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨21,by decide⟩).lower) ≤ (scalarRow12350.table ⟨21,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨21,by decide⟩).lower) ≤ 0.619003994005 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.514841347839 : ℝ)) (s := (0.857285475531 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.620995872286 : ℝ) ≤ 0.692708201025 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620995872286 : ℝ)) (Q := (0.620995872286 : ℝ))
      (s := (0.783813834150 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨21,by decide⟩).lower)
    (U := (0.787025318719 : ℝ)) (R := (0.787586306898 : ℝ)) (Q2 := (0.620995872286 : ℝ)) (T := (0.832762619076 : ℝ))
    (B := (scalarRow12350.table ⟨21,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy22 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨22,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨22,by decide⟩).lower) ≤ (scalarRow12350.table ⟨22,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨22,by decide⟩).lower) ≤ 0.618197779534 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513643316784 : ℝ)) (s := (0.858003813001 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.620188167713 : ℝ) ≤ 0.692129809989 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620188167713 : ℝ)) (Q := (0.620188167713 : ℝ))
      (s := (0.784453081216 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨22,by decide⟩).lower)
    (U := (0.786512961009 : ℝ)) (R := (0.787073949188 : ℝ)) (Q2 := (0.620188167713 : ℝ)) (T := (0.832414880289 : ℝ))
    (B := (scalarRow12350.table ⟨22,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy23 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨23,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨23,by decide⟩).lower) ≤ (scalarRow12350.table ⟨23,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨23,by decide⟩).lower) ≤ 0.617392115091 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512445285728 : ℝ)) (s := (0.858719878154 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.619381013807 : ℝ) ≤ 0.691552093178 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619381013807 : ℝ)) (Q := (0.619381013807 : ℝ))
      (s := (0.785090542381 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨23,by decide⟩).lower)
    (U := (0.786000619205 : ℝ)) (R := (0.786561607384 : ℝ)) (Q2 := (0.619381013807 : ℝ)) (T := (0.832067401784 : ℝ))
    (B := (scalarRow12350.table ⟨23,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy24 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨24,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨24,by decide⟩).lower) ≤ (scalarRow12350.table ⟨24,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨24,by decide⟩).lower) ≤ 0.616587000043 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511247254673 : ℝ)) (s := (0.859433676667 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.618574409938 : ℝ) ≤ 0.690975049327 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618574409938 : ℝ)) (Q := (0.618574409938 : ℝ))
      (s := (0.785726224184 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨24,by decide⟩).lower)
    (U := (0.785488292938 : ℝ)) (R := (0.786049281117 : ℝ)) (Q2 := (0.618574409938 : ℝ)) (T := (0.831720183126 : ℝ))
    (B := (scalarRow12350.table ⟨24,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy25 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨25,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨25,by decide⟩).lower) ≤ (scalarRow12350.table ⟨25,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨25,by decide⟩).lower) ≤ 0.615782433759 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510049223618 : ℝ)) (s := (0.860145214186 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.617768355473 : ℝ) ≤ 0.690398677169 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617768355473 : ℝ)) (Q := (0.617768355473 : ℝ))
      (s := (0.786360133130 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨25,by decide⟩).lower)
    (U := (0.784975981836 : ℝ)) (R := (0.785536970015 : ℝ)) (Q2 := (0.617768355473 : ℝ)) (T := (0.831373223878 : ℝ))
    (B := (scalarRow12350.table ⟨25,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy26 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨26,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨26,by decide⟩).lower) ≤ (scalarRow12350.table ⟨26,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨26,by decide⟩).lower) ≤ 0.614978415611 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.508851192563 : ℝ)) (s := (0.860854496316 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.616962849781 : ℝ) ≤ 0.689822975444 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616962849781 : ℝ)) (Q := (0.616962849781 : ℝ))
      (s := (0.786992275687 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨26,by decide⟩).lower)
    (U := (0.784463685527 : ℝ)) (R := (0.785024673706 : ℝ)) (Q2 := (0.616962849781 : ℝ)) (T := (0.831026523607 : ℝ))
    (B := (scalarRow12350.table ⟨26,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy27 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨27,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨27,by decide⟩).lower) ≤ (scalarRow12350.table ⟨27,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨27,by decide⟩).lower) ≤ 0.614174944973 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507653161507 : ℝ)) (s := (0.861561528629 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.616157892238 : ℝ) ≤ 0.689247942895 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616157892238 : ℝ)) (Q := (0.616157892238 : ℝ))
      (s := (0.787622658278 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨27,by decide⟩).lower)
    (U := (0.783951403643 : ℝ)) (R := (0.784512391822 : ℝ)) (Q2 := (0.616157892238 : ℝ)) (T := (0.830680081878 : ℝ))
    (B := (scalarRow12350.table ⟨27,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy28 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨28,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨28,by decide⟩).lower) ≤ (scalarRow12350.table ⟨28,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨28,by decide⟩).lower) ≤ 0.613372021226 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506455130452 : ℝ)) (s := (0.862266316656 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.615353482221 : ℝ) ≤ 0.688673578270 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615353482221 : ℝ)) (Q := (0.615353482221 : ℝ))
      (s := (0.788251287293 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨28,by decide⟩).lower)
    (U := (0.783439135815 : ℝ)) (R := (0.784000123994 : ℝ)) (Q2 := (0.615353482221 : ℝ)) (T := (0.830333898260 : ℝ))
    (B := (scalarRow12350.table ⟨28,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy29 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨29,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨29,by decide⟩).lower) ≤ (scalarRow12350.table ⟨29,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨29,by decide⟩).lower) ≤ 0.612569643749 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505257099397 : ℝ)) (s := (0.862968865898 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.614549619110 : ℝ) ≤ 0.688099880321 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614549619110 : ℝ)) (Q := (0.614549619110 : ℝ))
      (s := (0.788878169081 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨29,by decide⟩).lower)
    (U := (0.782926881675 : ℝ)) (R := (0.783487869854 : ℝ)) (Q2 := (0.614549619110 : ℝ)) (T := (0.829987972325 : ℝ))
    (B := (scalarRow12350.table ⟨29,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy30 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨30,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨30,by decide⟩).lower) ≤ (scalarRow12350.table ⟨30,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨30,by decide⟩).lower) ≤ 0.611767811928 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504059068341 : ℝ)) (s := (0.863669181819 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.613746302289 : ℝ) ≤ 0.687526847804 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613746302289 : ℝ)) (Q := (0.613746302289 : ℝ))
      (s := (0.789503309953 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨30,by decide⟩).lower)
    (U := (0.782414640858 : ℝ)) (R := (0.782975629037 : ℝ)) (Q2 := (0.613746302289 : ℝ)) (T := (0.829642303643 : ℝ))
    (B := (scalarRow12350.table ⟨30,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy31 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨31,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨31,by decide⟩).lower) ≤ (scalarRow12350.table ⟨31,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨31,by decide⟩).lower) ≤ 0.610966525152 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.502861037286 : ℝ)) (s := (0.864367269846 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.612943531144 : ℝ) ≤ 0.686954479478 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612943531144 : ℝ)) (Q := (0.612943531144 : ℝ))
      (s := (0.790126716185 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨31,by decide⟩).lower)
    (U := (0.781902412998 : ℝ)) (R := (0.782463401177 : ℝ)) (Q2 := (0.612943531144 : ℝ)) (T := (0.829296891788 : ℝ))
    (B := (scalarRow12350.table ⟨31,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy32 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨32,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨32,by decide⟩).lower) ≤ (scalarRow12350.table ⟨32,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨32,by decide⟩).lower) ≤ 0.610165782810 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501663006231 : ℝ)) (s := (0.865063135372 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.612141305066 : ℝ) ≤ 0.686382774111 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612141305066 : ℝ)) (Q := (0.612141305066 : ℝ))
      (s := (0.790748394012 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨32,by decide⟩).lower)
    (U := (0.781390197731 : ℝ)) (R := (0.781951185910 : ℝ)) (Q2 := (0.612141305066 : ℝ)) (T := (0.828951736335 : ℝ))
    (B := (scalarRow12350.table ⟨32,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy33 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨33,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨33,by decide⟩).lower) ≤ (scalarRow12350.table ⟨33,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨33,by decide⟩).lower) ≤ 0.609365584297 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500464975175 : ℝ)) (s := (0.865756783759 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.611339623448 : ℝ) ≤ 0.685811730470 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611339623448 : ℝ)) (Q := (0.611339623448 : ℝ))
      (s := (0.791368349635 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨33,by decide⟩).lower)
    (U := (0.780877994694 : ℝ)) (R := (0.781438982873 : ℝ)) (Q2 := (0.611339623448 : ℝ)) (T := (0.828606836862 : ℝ))
    (B := (scalarRow12350.table ⟨33,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy34 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨34,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨34,by decide⟩).lower) ≤ (scalarRow12350.table ⟨34,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨34,by decide⟩).lower) ≤ 0.608565929010 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499266944120 : ℝ)) (s := (0.866448220328 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.610538485685 : ℝ) ≤ 0.685241347327 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610538485685 : ℝ)) (Q := (0.610538485685 : ℝ))
      (s := (0.791986589216 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨34,by decide⟩).lower)
    (U := (0.780365803524 : ℝ)) (R := (0.780926791703 : ℝ)) (Q2 := (0.610538485685 : ℝ)) (T := (0.828262192945 : ℝ))
    (B := (scalarRow12350.table ⟨34,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy35 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨35,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨35,by decide⟩).lower) ≤ (scalarRow12350.table ⟨35,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨35,by decide⟩).lower) ≤ 0.607766816352 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498068913065 : ℝ)) (s := (0.867137450373 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.609737891181 : ℝ) ≤ 0.684671623464 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609737891181 : ℝ)) (Q := (0.609737891181 : ℝ))
      (s := (0.792603118880 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨35,by decide⟩).lower)
    (U := (0.779853623863 : ℝ)) (R := (0.780414612042 : ℝ)) (Q2 := (0.609737891181 : ℝ)) (T := (0.827917804168 : ℝ))
    (B := (scalarRow12350.table ⟨35,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy36 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨36,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨36,by decide⟩).lower) ≤ (scalarRow12350.table ⟨36,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨36,by decide⟩).lower) ≤ 0.606968245723 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496870882009 : ℝ)) (s := (0.867824479150 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.608937839333 : ℝ) ≤ 0.684102557660 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608937839333 : ℝ)) (Q := (0.608937839333 : ℝ))
      (s := (0.793217944722 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨36,by decide⟩).lower)
    (U := (0.779341455348 : ℝ)) (R := (0.779902443527 : ℝ)) (Q2 := (0.608937839333 : ℝ)) (T := (0.827573670110 : ℝ))
    (B := (scalarRow12350.table ⟨36,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy37 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨37,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨37,by decide⟩).lower) ≤ (scalarRow12350.table ⟨37,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨37,by decide⟩).lower) ≤ 0.606170216532 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.495672850954 : ℝ)) (s := (0.868509311883 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.608138329548 : ℝ) ≤ 0.683534148700 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608138329548 : ℝ)) (Q := (0.608138329548 : ℝ))
      (s := (0.793831072795 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨37,by decide⟩).lower)
    (U := (0.778829297621 : ℝ)) (R := (0.779390285800 : ℝ)) (Q2 := (0.608138329548 : ℝ)) (T := (0.827229790353 : ℝ))
    (B := (scalarRow12350.table ⟨37,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy38 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨38,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨38,by decide⟩).lower) ≤ (scalarRow12350.table ⟨38,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨38,by decide⟩).lower) ≤ 0.605372728190 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494474819899 : ℝ)) (s := (0.869191953763 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.607339361237 : ℝ) ≤ 0.682966395377 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607339361237 : ℝ)) (Q := (0.607339361237 : ℝ))
      (s := (0.794442509118 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨38,by decide⟩).lower)
    (U := (0.778317150325 : ℝ)) (R := (0.778878138504 : ℝ)) (Q2 := (0.607339361237 : ℝ)) (T := (0.826886164486 : ℝ))
    (B := (scalarRow12350.table ⟨38,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy39 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨39,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨39,by decide⟩).lower) ≤ (scalarRow12350.table ⟨39,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨39,by decide⟩).lower) ≤ 0.604575780108 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493276788844 : ℝ)) (s := (0.869872409948 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.606540933811 : ℝ) ≤ 0.682399296485 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606540933811 : ℝ)) (Q := (0.606540933811 : ℝ))
      (s := (0.795052259674 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨39,by decide⟩).lower)
    (U := (0.777805013103 : ℝ)) (R := (0.778366001282 : ℝ)) (Q2 := (0.606540933811 : ℝ)) (T := (0.826542792093 : ℝ))
    (B := (scalarRow12350.table ⟨39,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy40 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨40,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨40,by decide⟩).lower) ≤ (scalarRow12350.table ⟨40,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨40,by decide⟩).lower) ≤ 0.603779371703 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492078757788 : ℝ)) (s := (0.870550685563 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.605743046685 : ℝ) ≤ 0.681832850823 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605743046685 : ℝ)) (Q := (0.605743046685 : ℝ))
      (s := (0.795660330413 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨40,by decide⟩).lower)
    (U := (0.777292885599 : ℝ)) (R := (0.777853873778 : ℝ)) (Q2 := (0.605743046685 : ℝ)) (T := (0.826199672763 : ℝ))
    (B := (scalarRow12350.table ⟨40,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy41 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨41,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨41,by decide⟩).lower) ≤ (scalarRow12350.table ⟨41,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨41,by decide⟩).lower) ≤ 0.602983502397 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490880726733 : ℝ)) (s := (0.871226785701 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.604945699281 : ℝ) ≤ 0.681267057197 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604945699281 : ℝ)) (Q := (0.604945699281 : ℝ))
      (s := (0.796266727248 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨41,by decide⟩).lower)
    (U := (0.776780767461 : ℝ)) (R := (0.777341755640 : ℝ)) (Q2 := (0.604945699281 : ℝ)) (T := (0.825856806088 : ℝ))
    (B := (scalarRow12350.table ⟨41,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy42 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨42,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨42,by decide⟩).lower) ≤ (scalarRow12350.table ⟨42,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨42,by decide⟩).lower) ≤ 0.602188171609 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.489682695678 : ℝ)) (s := (0.871900715423 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.604148891016 : ℝ) ≤ 0.680701914412 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604148891016 : ℝ)) (Q := (0.604148891016 : ℝ))
      (s := (0.796871456061 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨42,by decide⟩).lower)
    (U := (0.776268658333 : ℝ)) (R := (0.776829646512 : ℝ)) (Q2 := (0.604148891016 : ℝ)) (T := (0.825514191658 : ℝ))
    (B := (scalarRow12350.table ⟨42,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy43 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨43,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨43,by decide⟩).lower) ≤ (scalarRow12350.table ⟨43,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨43,by decide⟩).lower) ≤ 0.601393378767 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488484664622 : ℝ)) (s := (0.872572479757 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.603352621316 : ℝ) ≤ 0.680137421281 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603352621316 : ℝ)) (Q := (0.603352621316 : ℝ))
      (s := (0.797474522698 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨43,by decide⟩).lower)
    (U := (0.775756557863 : ℝ)) (R := (0.776317546042 : ℝ)) (Q2 := (0.603352621316 : ℝ)) (T := (0.825171829068 : ℝ))
    (B := (scalarRow12350.table ⟨43,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy44 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨44,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨44,by decide⟩).lower) ≤ (scalarRow12350.table ⟨44,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨44,by decide⟩).lower) ≤ 0.600599123300 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487286633567 : ℝ)) (s := (0.873242083702 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.602556889610 : ℝ) ≤ 0.679573576622 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602556889610 : ℝ)) (Q := (0.602556889610 : ℝ))
      (s := (0.798075932969 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨44,by decide⟩).lower)
    (U := (0.775244465701 : ℝ)) (R := (0.775805453880 : ℝ)) (Q2 := (0.602556889610 : ℝ)) (T := (0.824829717913 : ℝ))
    (B := (scalarRow12350.table ⟨44,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy45 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨45,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨45,by decide⟩).lower) ≤ (scalarRow12350.table ⟨45,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨45,by decide⟩).lower) ≤ 0.599805404639 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486088602512 : ℝ)) (s := (0.873909532222 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.601761695329 : ℝ) ≤ 0.679010379255 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601761695329 : ℝ)) (Q := (0.601761695329 : ℝ))
      (s := (0.798675692654 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨45,by decide⟩).lower)
    (U := (0.774732381497 : ℝ)) (R := (0.775293369676 : ℝ)) (Q2 := (0.601761695329 : ℝ)) (T := (0.824487857790 : ℝ))
    (B := (scalarRow12350.table ⟨45,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy46 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨46,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨46,by decide⟩).lower) ≤ (scalarRow12350.table ⟨46,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨46,by decide⟩).lower) ≤ 0.599012222219 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484890571456 : ℝ)) (s := (0.874574830254 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.600967037905 : ℝ) ≤ 0.678447828003 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600967037905 : ℝ)) (Q := (0.600967037905 : ℝ))
      (s := (0.799273807498 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨46,by decide⟩).lower)
    (U := (0.774220304900 : ℝ)) (R := (0.774781293079 : ℝ)) (Q2 := (0.600967037905 : ℝ)) (T := (0.824146248297 : ℝ))
    (B := (scalarRow12350.table ⟨46,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy47 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨47,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨47,by decide⟩).lower) ≤ (scalarRow12350.table ⟨47,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨47,by decide⟩).lower) ≤ 0.598219575481 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.483692540401 : ℝ)) (s := (0.875237982700 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.600172916778 : ℝ) ≤ 0.677885921700 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600172916778 : ℝ)) (Q := (0.600172916778 : ℝ))
      (s := (0.799870283213 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨47,by decide⟩).lower)
    (U := (0.773708235565 : ℝ)) (R := (0.774269223744 : ℝ)) (Q2 := (0.600172916778 : ℝ)) (T := (0.823804889037 : ℝ))
    (B := (scalarRow12350.table ⟨47,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy48 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨48,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨48,by decide⟩).lower) ≤ (scalarRow12350.table ⟨48,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨48,by decide⟩).lower) ≤ 0.597427463864 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482494509346 : ℝ)) (s := (0.875898994435 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.599379331388 : ℝ) ≤ 0.677324659177 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599379331388 : ℝ)) (Q := (0.599379331388 : ℝ))
      (s := (0.800465125477 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨48,by decide⟩).lower)
    (U := (0.773196173144 : ℝ)) (R := (0.773757161323 : ℝ)) (Q2 := (0.599379331388 : ℝ)) (T := (0.823463779610 : ℝ))
    (B := (scalarRow12350.table ⟨48,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy49 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨49,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨49,by decide⟩).lower) ≤ (scalarRow12350.table ⟨49,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨49,by decide⟩).lower) ≤ 0.596635886813 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481296478290 : ℝ)) (s := (0.876557870301 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.598586281178 : ℝ) ≤ 0.676764039273 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598586281178 : ℝ)) (Q := (0.598586281178 : ℝ))
      (s := (0.801058339939 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨49,by decide⟩).lower)
    (U := (0.772684117291 : ℝ)) (R := (0.773245105470 : ℝ)) (Q2 := (0.598586281178 : ℝ)) (T := (0.823122919622 : ℝ))
    (B := (scalarRow12350.table ⟨49,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy50 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨50,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨50,by decide⟩).lower) ≤ (scalarRow12350.table ⟨50,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨50,by decide⟩).lower) ≤ 0.595844843776 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480098447235 : ℝ)) (s := (0.877214615110 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.597793765594 : ℝ) ≤ 0.676204060830 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597793765594 : ℝ)) (Q := (0.597793765594 : ℝ))
      (s := (0.801649932213 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨50,by decide⟩).lower)
    (U := (0.772172067661 : ℝ)) (R := (0.772733055840 : ℝ)) (Q2 := (0.597793765594 : ℝ)) (T := (0.822782308676 : ℝ))
    (B := (scalarRow12350.table ⟨50,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy51 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨51,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨51,by decide⟩).lower) ≤ (scalarRow12350.table ⟨51,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨51,by decide⟩).lower) ≤ 0.595054334205 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478900416180 : ℝ)) (s := (0.877869233647 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.597001784089 : ℝ) ≤ 0.675644722698 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597001784089 : ℝ)) (Q := (0.597001784089 : ℝ))
      (s := (0.802239907880 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨51,by decide⟩).lower)
    (U := (0.771660023913 : ℝ)) (R := (0.772221012092 : ℝ)) (Q2 := (0.597001784089 : ℝ)) (T := (0.822441946384 : ℝ))
    (B := (scalarRow12350.table ⟨51,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy52 :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table ⟨52,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table ⟨52,by decide⟩).lower) ≤ (scalarRow12350.table ⟨52,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow12350.table ⟨52,by decide⟩).lower) ≤ 0.594264357552 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.477702385125 : ℝ)) (s := (0.878521730663 : ℝ))
      <;> norm_num [scalarRow12350,cell12350]
  have hk2 : kappa (0.596210336111 : ℝ) ≤ 0.675086023724 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596210336111 : ℝ)) (Q := (0.596210336111 : ℝ))
      (s := (0.802828272494 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow12350.table ⟨52,by decide⟩).lower)
    (U := (0.771147985702 : ℝ)) (R := (0.771708973881 : ℝ)) (Q2 := (0.596210336111 : ℝ)) (T := (0.822101832352 : ℝ))
    (B := (scalarRow12350.table ⟨52,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow12350,cell12350])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12350 (gMinus 12350) (1 - (scalarRow12350.table i).lower) ≤ 1 ∧
    energyUpper 12350 (gMinus 12350) (BstLean.Part211.gPlus 12350)
      (finiteEnergy 12350 12350 0.011) (1 - (scalarRow12350.table i).lower) ≤
      (scalarRow12350.table i).energy := by
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
  | ⟨10,h⟩ => exact pilot_upperEnergy10
  | ⟨11,h⟩ => exact pilot_upperEnergy11
  | ⟨12,h⟩ => exact pilot_upperEnergy12
  | ⟨13,h⟩ => exact pilot_upperEnergy13
  | ⟨14,h⟩ => exact pilot_upperEnergy14
  | ⟨15,h⟩ => exact pilot_upperEnergy15
  | ⟨16,h⟩ => exact pilot_upperEnergy16
  | ⟨17,h⟩ => exact pilot_upperEnergy17
  | ⟨18,h⟩ => exact pilot_upperEnergy18
  | ⟨19,h⟩ => exact pilot_upperEnergy19
  | ⟨20,h⟩ => exact pilot_upperEnergy20
  | ⟨21,h⟩ => exact pilot_upperEnergy21
  | ⟨22,h⟩ => exact pilot_upperEnergy22
  | ⟨23,h⟩ => exact pilot_upperEnergy23
  | ⟨24,h⟩ => exact pilot_upperEnergy24
  | ⟨25,h⟩ => exact pilot_upperEnergy25
  | ⟨26,h⟩ => exact pilot_upperEnergy26
  | ⟨27,h⟩ => exact pilot_upperEnergy27
  | ⟨28,h⟩ => exact pilot_upperEnergy28
  | ⟨29,h⟩ => exact pilot_upperEnergy29
  | ⟨30,h⟩ => exact pilot_upperEnergy30
  | ⟨31,h⟩ => exact pilot_upperEnergy31
  | ⟨32,h⟩ => exact pilot_upperEnergy32
  | ⟨33,h⟩ => exact pilot_upperEnergy33
  | ⟨34,h⟩ => exact pilot_upperEnergy34
  | ⟨35,h⟩ => exact pilot_upperEnergy35
  | ⟨36,h⟩ => exact pilot_upperEnergy36
  | ⟨37,h⟩ => exact pilot_upperEnergy37
  | ⟨38,h⟩ => exact pilot_upperEnergy38
  | ⟨39,h⟩ => exact pilot_upperEnergy39
  | ⟨40,h⟩ => exact pilot_upperEnergy40
  | ⟨41,h⟩ => exact pilot_upperEnergy41
  | ⟨42,h⟩ => exact pilot_upperEnergy42
  | ⟨43,h⟩ => exact pilot_upperEnergy43
  | ⟨44,h⟩ => exact pilot_upperEnergy44
  | ⟨45,h⟩ => exact pilot_upperEnergy45
  | ⟨46,h⟩ => exact pilot_upperEnergy46
  | ⟨47,h⟩ => exact pilot_upperEnergy47
  | ⟨48,h⟩ => exact pilot_upperEnergy48
  | ⟨49,h⟩ => exact pilot_upperEnergy49
  | ⟨50,h⟩ => exact pilot_upperEnergy50
  | ⟨51,h⟩ => exact pilot_upperEnergy51
  | ⟨52,h⟩ => exact pilot_upperEnergy52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12350

/-! Source-cell containment and simple scalar guards at 12350. -/
namespace BstLean.Part269.N12350
open BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12350)
open BstLean.Part268 (cell12350)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨10,by decide⟩).lower ∧ (scalarRow12350.table ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (scalarRow12350.table ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨11,by decide⟩).lower ∧ (scalarRow12350.table ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (scalarRow12350.table ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨12,by decide⟩).lower ∧ (scalarRow12350.table ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (scalarRow12350.table ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨13,by decide⟩).lower ∧ (scalarRow12350.table ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (scalarRow12350.table ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨14,by decide⟩).lower ∧ (scalarRow12350.table ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (scalarRow12350.table ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨15,by decide⟩).lower ∧ (scalarRow12350.table ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (scalarRow12350.table ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨16,by decide⟩).lower ∧ (scalarRow12350.table ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (scalarRow12350.table ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨17,by decide⟩).lower ∧ (scalarRow12350.table ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (scalarRow12350.table ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨18,by decide⟩).lower ∧ (scalarRow12350.table ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (scalarRow12350.table ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨19,by decide⟩).lower ∧ (scalarRow12350.table ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (scalarRow12350.table ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨20,by decide⟩).lower ∧ (scalarRow12350.table ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (scalarRow12350.table ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨21,by decide⟩).lower ∧ (scalarRow12350.table ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (scalarRow12350.table ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨22,by decide⟩).lower ∧ (scalarRow12350.table ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (scalarRow12350.table ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨23,by decide⟩).lower ∧ (scalarRow12350.table ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (scalarRow12350.table ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨24,by decide⟩).lower ∧ (scalarRow12350.table ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (scalarRow12350.table ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨25,by decide⟩).lower ∧ (scalarRow12350.table ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (scalarRow12350.table ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨26,by decide⟩).lower ∧ (scalarRow12350.table ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (scalarRow12350.table ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨27,by decide⟩).lower ∧ (scalarRow12350.table ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (scalarRow12350.table ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨28,by decide⟩).lower ∧ (scalarRow12350.table ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (scalarRow12350.table ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨29,by decide⟩).lower ∧ (scalarRow12350.table ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (scalarRow12350.table ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨30,by decide⟩).lower ∧ (scalarRow12350.table ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (scalarRow12350.table ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨31,by decide⟩).lower ∧ (scalarRow12350.table ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (scalarRow12350.table ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨32,by decide⟩).lower ∧ (scalarRow12350.table ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (scalarRow12350.table ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨33,by decide⟩).lower ∧ (scalarRow12350.table ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (scalarRow12350.table ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨34,by decide⟩).lower ∧ (scalarRow12350.table ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (scalarRow12350.table ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨35,by decide⟩).lower ∧ (scalarRow12350.table ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (scalarRow12350.table ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨36,by decide⟩).lower ∧ (scalarRow12350.table ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (scalarRow12350.table ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨37,by decide⟩).lower ∧ (scalarRow12350.table ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (scalarRow12350.table ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨38,by decide⟩).lower ∧ (scalarRow12350.table ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (scalarRow12350.table ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨39,by decide⟩).lower ∧ (scalarRow12350.table ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (scalarRow12350.table ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨40,by decide⟩).lower ∧ (scalarRow12350.table ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (scalarRow12350.table ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨41,by decide⟩).lower ∧ (scalarRow12350.table ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (scalarRow12350.table ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨42,by decide⟩).lower ∧ (scalarRow12350.table ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (scalarRow12350.table ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨43,by decide⟩).lower ∧ (scalarRow12350.table ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (scalarRow12350.table ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨44,by decide⟩).lower ∧ (scalarRow12350.table ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (scalarRow12350.table ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨45,by decide⟩).lower ∧ (scalarRow12350.table ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (scalarRow12350.table ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨46,by decide⟩).lower ∧ (scalarRow12350.table ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (scalarRow12350.table ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨47,by decide⟩).lower ∧ (scalarRow12350.table ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (scalarRow12350.table ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨48,by decide⟩).lower ∧ (scalarRow12350.table ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (scalarRow12350.table ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨49,by decide⟩).lower ∧ (scalarRow12350.table ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (scalarRow12350.table ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨50,by decide⟩).lower ∧ (scalarRow12350.table ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (scalarRow12350.table ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨51,by decide⟩).lower ∧ (scalarRow12350.table ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (scalarRow12350.table ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (scalarRow12350.table ⟨52,by decide⟩).lower ∧ (scalarRow12350.table ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (scalarRow12350.table ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12350.table ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12350,cell12350,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (scalarRow12350.table i).lower ∧
    (scalarRow12350.table i).upper ≤ groupTheta (centreGroup i) ∧
    (scalarRow12350.table i).upper ≤ (0.532 : ℝ) ∧
    (scalarRow12350.table i).centre ≤ (0.1 : ℝ) ∧ (scalarRow12350.table i).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12350.table i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12350.table i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12350

/-! The local source numeric instances at 12350 have no network premises. -/
namespace BstLean.Part269.N12350
open BstLean.Part264
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12350)
open BstLean.Part268 (cell12350)

noncomputable def sourceNumerics12350 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12350 (scalarRow12350.table i)
      scalarRow12350.M scalarRow12350.H scalarRow12350.xi := by
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
    energy_allowance := scalarRow12350.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12350]
    centre_nonneg := (scalarRow12350.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part264.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12350])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12350