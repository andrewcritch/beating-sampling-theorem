import BstLean.Part269Source
import BstLean.Part269Direction34
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
import BstLean.Part264HS
import BstLean.Part264Source
import BstLean.Part264bSourceCommon
import BstLean.Part269Finite
import BstLean.Part269Row13224
/-! Actual 13224 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13224
open BstLean.Part264
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13224 ≤ (1.035086404142 : ℝ) := by
  have hr : (114.995652091720 : ℝ) ≤ √(13224 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.995652091720 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13224 13224 (11 / 1000) ≤
    (0.008312374130 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13224) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.995652091720 : ℝ) ≤ √(13224 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13224)
  have hdiv : K / √(13224 : ℝ) ≤ K / 114.995652091720 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.995652091720 ≤ (0.008312374130 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13224.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13224 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13224 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13224 := gPlus_lower 13224
end BstLean.Part269.N13224

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13224
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035086404141 : ℝ) ≤ wn 13224 := by
  have hn : √(13224 : ℝ) ≤ 114.995652091721 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13224 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.995652091721 ≤ 2 / √(13224 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_cs_upper : csC ≤ 1.295212 := by
  have hp := pi_lt_d6.le
  have hd : (1 : ℝ) / 3.141593 ≤ 1 / π := by gcongr
  unfold csC
  linarith

theorem pilot_rho_bounds : (0.000241731304 : ℝ) ≤ rhoBar 13224 csC ∧
    rhoBar 13224 csC ≤ 0.000241731678 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := pilot_cs_upper
  have hc0 : 0 < csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035086404141 : ℝ) / (1.295212 * 13224) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035086404142 : ℝ) / (1.29521 * 13224) := by gcongr
      _ ≤ (0.000241731678 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13224 csC) ≤ 0.000966985147 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13224 csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13224 csC) :=
    le_sqrt_of_sq_le (by linarith)
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √2 ≤ 0.707106782 := by
    calc
      _ ≤ (1 : ℝ) / 1.414213562 := by gcongr
      _ ≤ (0.707106782 : ℝ) := by norm_num
  have hgap : (0.292631318 : ℝ) ≤ √(1 - 2 * rhoBar 13224 csC) - 1 / √2 := by linarith
  have hexp : (100 : ℝ) ≤ (√(1 - 2 * rhoBar 13224 csC) - 1 / √2) ^ 2 /
      (2 * rhoBar 13224 csC) := by
    apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13224 csC)).mpr
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

theorem pilot_cc_bounds : cc0 (rhoBar 13224 csC) (piBar (rhoBar 13224 csC)) ≤ 0.000184635940 ∧
    cc1 (rhoBar 13224 csC) (piBar (rhoBar 13224 csC)) ≤ 0.000117485146 ∧
    cc2 (rhoBar 13224 csC) ≤ 0.000068201114 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13224 csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13224 csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13224 csC) := by unfold piBar; positivity
  have hz := pilot_phi_zero_upper
  have ho := pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13224 csC * nuR (rhoBar 13224 csC)) ≤ 0.000483477965 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000241731678 : ℝ) * 0.000966985147 := by gcongr
      _ ≤ (0.000483477965 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13224 csC) * nuR (rhoBar 13224 csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000966985147 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13224 csC) * rhoBar 13224 csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000241731678 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000241731678 / 2 + 0.399 * 0.000966985147 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000184635940 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000483477965 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000117485146 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000241731678 / 1.414213562 := by gcongr
      _ ≤ (0.000068201114 : ℝ) := by norm_num

end BstLean.Part269.N13224

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13224
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13224 csC) (piBar (rhoBar 13224 csC)) ≤ 1.47221E-7 := by
  have hr0 : 0 ≤ rhoBar 13224 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13224 csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13224 csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13224 csC) (piBar (rhoBar 13224 csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13224 csC) (piBar (rhoBar 13224 csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13224 csC) := by unfold cc2; positivity
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
    _ ≤ (0.000184635940 : ℝ) ^ 2 + 0.000117485146 ^ 2 + 3 * 0.000068201114 ^ 2 +
        2 * 0.797885 * 0.000184635940 * 0.000117485146 + 2 * 0.000184635940 * 0.000068201114 +
        4 * 0.797885 * 0.000117485146 * 0.000068201114 := by gcongr
    _ ≤ (1.47221E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13224 csC Θ ≤ 0.002521584139 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13224 csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13224 csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13224 csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13224 csC) (piBar (rhoBar 13224 csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13224 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035086404142 * 1.47221E-7 / (0.000241731304 : ℝ) := by gcongr
    _ ≤ 0.002521584139 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13224 csC Θ ≤ 0.002795870313 + 0.000637162747 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13224 csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13224 csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13224 csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035086404142 : ℝ) * ((2 * Θ * 0.000241731678 +
        (6863 / 10000) * 0.000241731678 * 13224 * 0.000966985147) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002795870313 + 0.000637162747 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13224 csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13224 csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13224 0.011 Θ ∧ gammaRatio 13224 0.011 Θ ≤ 0.000090016 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13224 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035086404142 : ℝ) * 0.525 / ((1 - 0.011) * 13224) := by gcongr
      _ ≤ (0.000090016 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13224 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13224 0.011 Θ) :=
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
    badAllowance 13224 csC 0.011 1.22 1.12 Θ ≤ 0.0011 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13224 csC) 1.22 ≤ 0.0000000153 := by
    have he : (18 : ℝ) ≤ gap 2 (rhoBar 13224 csC) 1.22 ^ 2 / (2 * rhoBar 13224 csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13224 csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ (show exp (-18 : ℝ) ≤ 0.0000000153 from
      by simpa only [Nat.cast_ofNat] using exp_negative_bound 18 (by norm_num :
        ((2.71828 : ℝ) ^ 18)⁻¹ ≤ 0.0000000153))
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13224 0.011 Θ) 1.12 ≤ 0.0000000506 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 13224 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13224 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13224 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ exp_minus_168_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13224 csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13224 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035086404142 : ℝ) * 13224 *
        (0.0000000153 / 1.1045361 + 0.0000000506 / 1.05830052) := by gcongr
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
    momentAllowance 13224 csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003895870313 + 0.003158746886 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13224

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13224
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13224 csC) (piBar (rhoBar 13224 csC)) := by
  have hr0 : 0 ≤ rhoBar 13224 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13224 csC)
  have hv0 : 0 ≤ nuR (rhoBar 13224 csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13224 csC Θ := by
  have hr0 : 0 ≤ rhoBar 13224 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13224 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13224 csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13224 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13224 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13224 csC)
  have hv0 : 0 ≤ nuR (rhoBar 13224 csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13224 csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13224 csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13224 csC 0.011 0.46 Θ ≤ 0.051422797580 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / 13224) ≤ 0.010385067256 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13224 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035086404142)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010385067256 + 2 * 0.737676 / 13224) := by gcongr
    _ ≤ (0.051422797580 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13224 12 ≤ 0.0015 := by
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar 13224 12 ≤ 0.000749634 := by
    unfold N12bar
    simp only [Nat.cast_ofNat]
    linarith
  have h10 : 0 ≤ N12bar 13224 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem pilot_radial_centre_bound {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 114.995652091720 ≤ R) : xiNr 13224 Θ 1.22 ≤ R := by
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hn := pilot_n22_upper
  have hn0 : 0 ≤ N22bar 13224 12 := by unfold N22bar N12bar; positivity
  have hN : (114.995652091720 : ℝ) ≤ √(13224 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold xiNr
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  gcongr
  linarith

theorem pilot_full_formula_bound {Θ S X T R B : ℝ}
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.003895870313 + 0.003158746886 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 114.995652091720 ≤ R)
    (hB : (X + 0.051422797580 + R + 0.008312374130) ^ 2 ≤ B) :
    fullFormula 13224 13224 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance 13224 csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, (pilot_moment_upper hw hS).trans hXsq⟩
  have hd := pilot_deviation_upper hΘ hw.2
  have hr := pilot_radial_centre_bound hΘ hT hTsq hR
  have hf : finiteEnergy 13224 13224 0.011 ≤ 0.008312374130 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation 13224 csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar 13224 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr 13224 Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg 13224 13224 (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

end BstLean.Part269.N13224

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13224
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560526326141 : ℝ) ≤ plow 13224 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13224) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060812429)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001323831673) : eMP 13224 0.011 xi bn ≤ 0.001140570878 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13224 : ℝ) * (1 - 0.011))) ≤ 0.000563912574 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001323831673 / (13224 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000563912574 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000563912574 : ℝ) + 3.141593 * 0.053060812429 / (13224 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001140570878 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060812429)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001323831673) : PiBarMP 13224 12 0.011 xi bn ≤ 0.157998870300 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13224 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036384497702 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.361427063498 : ℝ) ≤ √((13224 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.995652091720 : ℝ) ≤ √(13224 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13224) ≤ 0.121155956850 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036384497702 + 0.053060812429 * 1.772454 / (2 * (114.361427063498 : ℝ))) * (1 + 0.001140570878) +
        8 / (13224 * 114.995652091720) + 0.121155956850 := by gcongr
    _ ≤ (0.157998870300 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060812429)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001323831673) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281772124536) :
    parallelOracle 13224 0.011 xi bn cd ≤ 0.158960077860 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13224 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13224 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560526326141 : ℝ) ≤ plow 13224 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.995652091720 : ℝ) ≤ √(13224 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.281772124536 : ℝ) / (2 * 0.560526326141 * 114.995652091720)) * 0.157998870300 +
        0.281772124536 ^ 2 / (2 * 0.560526326141 * 114.995652091720) := by gcongr
    _ ≤ (0.158960077860 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053060812429) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001323831673)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.281772124536) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13224 13224 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560526326141 : ℝ) ≤ plow 13224 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.995652091720 : ℝ) ≤ √(13224 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13224 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13224 Θ 1.22 ≤ 0.011531744687 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.995652091720 := by gcongr <;> linarith
      _ ≤ (0.011531744687 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13224 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13224 13224 0.011 ≤ 0.008312374130 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13224 13224 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13224 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13224 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13224 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13224 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.158960077860 + 0.011531744687 + (0.008312374130 : ℝ) *
        (1 + 2 * (0.281772124536 + 0.011531744687) / (0.560526326141 * 114.995652091720))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13224]

end BstLean.Part269.N13224

/-! The original eight local profiles supply actual 13224 moment certificates. -/
namespace BstLean.Part269.N13224
open BstLean.Part264
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13224 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13224 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13224 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053060812429 ∧
    0 ≤ bN 13224 csC (groupTheta g) ∧ bN 13224 csC (groupTheta g) ≤ 0.001323831673 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13224 13224 0.011
      (momentAllowance 13224 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13224 csC (groupTheta g))
      (√(momentAllowance 13224 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13224 csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13224 csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13224 csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230349326956 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13224 0.011
      (momentAllowance 13224 csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13224 csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13224
/-! The actual computed-centre upper energy formula at 13224. -/
namespace BstLean.Part269.N13224
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem pilot_energy_upper_from_kappas {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 13224 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 13224 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 13224 + 0.008312374130 / 114.995652091720) ^ 2 ≤ B) :
    energyRatio 13224 (gMinus 13224) q ≤ Q2 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 (11 / 1000)) q ≤ B := by
  have hs : √(kappa q + 5 / (13224 : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot 13224 q ≤ R := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hm0 : 0 ≤ meanRoot 13224 q := by unfold meanRoot; positivity
  have hR0 : 0 ≤ R := hm0.trans hm
  have hg := pilot_gMinus_lower
  have hg0 : 0 < gMinus 13224 := by linarith
  have hratio : energyRatio 13224 (gMinus 13224) q ≤ Q2 := by
    unfold energyRatio
    apply le_trans ?_ hQ2
    gcongr
  have hr0 : 0 ≤ energyRatio 13224 (gMinus 13224) q := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) hg0.le
  have hQ20 : 0 ≤ Q2 := hr0.trans hratio
  have hk := kappa_monotoneOn
    (show energyRatio 13224 (gMinus 13224) q ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show Q2 ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩) hratio
  have hk' := hk.trans hK2
  have hk0 := (kappa_mem (by linarith : -1 ≤ energyRatio 13224 (gMinus 13224) q)
    (by linarith : energyRatio 13224 (gMinus 13224) q ≤ 1)).1
  have hgp := pilot_gPlus_upper
  have hgp0 : 0 ≤ BstLean.Part211.gPlus 13224 := le_trans zero_le_one pilot_gPlus_lower
  have ht : √(BstLean.Part211.gPlus 13224 * kappa (energyRatio 13224 (gMinus 13224) q)) ≤ T := by
    apply sqrt_le_iff.mpr
    refine ⟨hT, ?_⟩
    exact (mul_le_mul hgp hk' hk0 (by norm_num)).trans hTsq
  have ht2 : √(12 * BstLean.Part211.gPlus 13224) ≤ 3.466066 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hn : (114.995652091720 : ℝ) ≤ √(13224 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hf := pilot_finite_centre_upper
  have hf0 := finiteEnergy_nonneg 13224 13224 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hB
  gcongr


end BstLean.Part269.N13224

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13224
open BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13224)
open BstLean.Part269 (cell13224)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085088493961
  | 2 => 0.086008106878
  | 3 => 0.086922924545
  | 4 => 0.087833662554
  | 5 => 0.088741205200
  | 6 => 0.089646632766
  | 7 => 0.090551251809
  | 8 => 0.091456628574
  | _ => 0

theorem pilot_fullGroup1 :
    fullFormula 13224 13224 0.011 1.22 1.12 0.46 (groupTheta 1)
      (groupProfile 1) 1.22 ≤ pilotGroupCentre 1 := by
  apply pilot_full_formula_bound (X := (0.219798646013 : ℝ)) (T := (0.760762628683 : ℝ)) (R := (0.010747080052 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup2 :
    fullFormula 13224 13224 0.011 1.22 1.12 0.46 (groupTheta 2)
      (groupProfile 2) 1.22 ≤ pilotGroupCentre 2 := by
  apply pilot_full_formula_bound (X := (0.221362080570 : ℝ)) (T := (0.766511359721 : ℝ)) (R := (0.010859746529 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup3 :
    fullFormula 13224 13224 0.011 1.22 1.12 0.46 (groupTheta 3)
      (groupProfile 3) 1.22 ≤ pilotGroupCentre 3 := by
  apply pilot_full_formula_bound (X := (0.222905176338 : ℝ)) (T := (0.772217296608 : ℝ)) (R := (0.010972040877 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup4 :
    fullFormula 13224 13224 0.011 1.22 1.12 0.46 (groupTheta 4)
      (groupProfile 4) 1.22 ≤ pilotGroupCentre 4 := by
  apply pilot_full_formula_bound (X := (0.224428136145 : ℝ)) (T := (0.777881379492 : ℝ)) (R := (0.011083971255 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup5 :
    fullFormula 13224 13224 0.011 1.22 1.12 0.46 (groupTheta 5)
      (groupProfile 5) 1.22 ≤ pilotGroupCentre 5 := by
  apply pilot_full_formula_bound (X := (0.225931157862 : ℝ)) (T := (0.783504517639 : ℝ)) (R := (0.011195545588 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup6 :
    fullFormula 13224 13224 0.011 1.22 1.12 0.46 (groupTheta 6)
      (groupProfile 6) 1.22 ≤ pilotGroupCentre 6 := by
  apply pilot_full_formula_bound (X := (0.227414432907 : ℝ)) (T := (0.789087584835 : ℝ)) (R := (0.011306771455 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup7 :
    fullFormula 13224 13224 0.011 1.22 1.12 0.46 (groupTheta 7)
      (groupProfile 7) 1.22 ≤ pilotGroupCentre 7 := by
  apply pilot_full_formula_bound (X := (0.228878148094 : ℝ)) (T := (0.794631427230 : ℝ)) (R := (0.011417656233 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_fullGroup8 :
    fullFormula 13224 13224 0.011 1.22 1.12 0.46 (groupTheta 8)
      (groupProfile 8) 1.22 ≤ pilotGroupCentre 8 := by
  apply pilot_full_formula_bound (X := (0.230322484175 : ℝ)) (T := (0.800136858619 : ℝ)) (R := (0.011528206981 : ℝ))
    <;> norm_num [groupTheta,groupProfile,pilotGroupCentre]

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13224 13224 0.011 1.22 1.12 0.46 (groupTheta g)
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

end BstLean.Part269.N13224

/-! Actual upper energy certificates on all 43 source endpoints at 13224. -/
namespace BstLean.Part269.N13224
open BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13224)
open BstLean.Part269 (cell13224)
theorem pilot_upperEnergy10 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨10,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨10,by decide⟩).lower) ≤ (scalarRow13224.table ⟨10,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨10,by decide⟩).lower) ≤ 0.627971674481 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.528112327099 : ℝ)) (s := (0.849174522679 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.629894407787 : ℝ) ≤ 0.699098990395 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629894407787 : ℝ)) (Q := (0.629894407787 : ℝ))
      (s := (0.776680780655 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨10,by decide⟩).lower)
    (U := (0.792685167582 : ℝ)) (R := (0.793209078956 : ℝ)) (Q2 := (0.629894407787 : ℝ)) (T := (0.836595251510 : ℝ))
    (B := (scalarRow13224.table ⟨10,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy11 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨11,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨11,by decide⟩).lower) ≤ (scalarRow13224.table ⟨11,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨11,by decide⟩).lower) ≤ 0.627165603175 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.526923559808 : ℝ)) (s := (0.849912679115 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.629086888512 : ℝ) ≤ 0.698517629965 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.629086888512 : ℝ)) (Q := (0.629086888512 : ℝ))
      (s := (0.777334990016 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨11,by decide⟩).lower)
    (U := (0.792176560875 : ℝ)) (R := (0.792700472249 : ℝ)) (Q2 := (0.629086888512 : ℝ)) (T := (0.836247329015 : ℝ))
    (B := (scalarRow13224.table ⟨11,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy12 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨12,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨12,by decide⟩).lower) ≤ (scalarRow13224.table ⟨12,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨12,by decide⟩).lower) ≤ 0.626360080555 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.525734792518 : ℝ)) (s := (0.850648533730 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.628279918565 : ℝ) ≤ 0.697936947430 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.628279918565 : ℝ)) (Q := (0.628279918565 : ℝ))
      (s := (0.777987367461 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨12,by decide⟩).lower)
    (U := (0.791667973951 : ℝ)) (R := (0.792191885325 : ℝ)) (Q2 := (0.628279918565 : ℝ)) (T := (0.835899667653 : ℝ))
    (B := (scalarRow13224.table ⟨12,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy13 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨13,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨13,by decide⟩).lower) ≤ (scalarRow13224.table ⟨13,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨13,by decide⟩).lower) ≤ 0.625555105965 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.524546025228 : ℝ)) (s := (0.851382092493 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.627473497289 : ℝ) ≤ 0.697356941502 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.627473497289 : ℝ)) (Q := (0.627473497289 : ℝ))
      (s := (0.778637919832 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨13,by decide⟩).lower)
    (U := (0.791159406434 : ℝ)) (R := (0.791683317808 : ℝ)) (Q2 := (0.627473497289 : ℝ)) (T := (0.835552266980 : ℝ))
    (B := (scalarRow13224.table ⟨13,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy14 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨14,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨14,by decide⟩).lower) ≤ (scalarRow13224.table ⟨14,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨14,by decide⟩).lower) ≤ 0.624750678756 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.523357257938 : ℝ)) (s := (0.852113361334 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.626667624037 : ℝ) ≤ 0.696777610905 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.626667624037 : ℝ)) (Q := (0.626667624037 : ℝ))
      (s := (0.779286653924 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨14,by decide⟩).lower)
    (U := (0.790650857952 : ℝ)) (R := (0.791174769326 : ℝ)) (Q2 := (0.626667624037 : ℝ)) (T := (0.835205126556 : ℝ))
    (B := (scalarRow13224.table ⟨14,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy15 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨15,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨15,by decide⟩).lower) ≤ (scalarRow13224.table ⟨15,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨15,by decide⟩).lower) ≤ 0.623946798280 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.522168490648 : ℝ)) (s := (0.852842346143 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.625862298157 : ℝ) ≤ 0.696198954361 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625862298157 : ℝ)) (Q := (0.625862298157 : ℝ))
      (s := (0.779933576496 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨15,by decide⟩).lower)
    (U := (0.790142328131 : ℝ)) (R := (0.790666239505 : ℝ)) (Q2 := (0.625862298157 : ℝ)) (T := (0.834858245939 : ℝ))
    (B := (scalarRow13224.table ⟨15,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy16 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨16,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨16,by decide⟩).lower) ≤ (scalarRow13224.table ⟨16,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨16,by decide⟩).lower) ≤ 0.623143463892 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.520979723358 : ℝ)) (s := (0.853569052772 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.625057519004 : ℝ) ≤ 0.695620970595 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.625057519004 : ℝ)) (Q := (0.625057519004 : ℝ))
      (s := (0.780578694263 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨16,by decide⟩).lower)
    (U := (0.789633816599 : ℝ)) (R := (0.790157727973 : ℝ)) (Q2 := (0.625057519004 : ℝ)) (T := (0.834511624688 : ℝ))
    (B := (scalarRow13224.table ⟨16,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy17 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨17,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨17,by decide⟩).lower) ≤ (scalarRow13224.table ⟨17,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨17,by decide⟩).lower) ≤ 0.622340674951 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.519790956067 : ℝ)) (s := (0.854293487036 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.624253285934 : ℝ) ≤ 0.695043658340 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.624253285934 : ℝ)) (Q := (0.624253285934 : ℝ))
      (s := (0.781222013900 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨17,by decide⟩).lower)
    (U := (0.789125322984 : ℝ)) (R := (0.789649234358 : ℝ)) (Q2 := (0.624253285934 : ℝ)) (T := (0.834165262367 : ℝ))
    (B := (scalarRow13224.table ⟨17,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy18 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨18,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨18,by decide⟩).lower) ≤ (scalarRow13224.table ⟨18,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨18,by decide⟩).lower) ≤ 0.621538430819 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.518602188777 : ℝ)) (s := (0.855015654708 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.623449598310 : ℝ) ≤ 0.694467016331 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.623449598310 : ℝ)) (Q := (0.623449598310 : ℝ))
      (s := (0.781863542038 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨18,by decide⟩).lower)
    (U := (0.788616846918 : ℝ)) (R := (0.789140758292 : ℝ)) (Q2 := (0.623449598310 : ℝ)) (T := (0.833819158538 : ℝ))
    (B := (scalarRow13224.table ⟨18,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy19 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨19,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨19,by decide⟩).lower) ≤ (scalarRow13224.table ⟨19,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨19,by decide⟩).lower) ≤ 0.620736730861 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.517413421487 : ℝ)) (s := (0.855735561529 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.622646455496 : ℝ) ≤ 0.693891043308 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.622646455496 : ℝ)) (Q := (0.622646455496 : ℝ))
      (s := (0.782503285270 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨19,by decide⟩).lower)
    (U := (0.788108388031 : ℝ)) (R := (0.788632299405 : ℝ)) (Q2 := (0.622646455496 : ℝ)) (T := (0.833473312768 : ℝ))
    (B := (scalarRow13224.table ⟨19,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy20 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨20,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨20,by decide⟩).lower) ≤ (scalarRow13224.table ⟨20,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨20,by decide⟩).lower) ≤ 0.619935574443 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.516224654197 : ℝ)) (s := (0.856453213200 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.621843856856 : ℝ) ≤ 0.693315738012 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621843856856 : ℝ)) (Q := (0.621843856856 : ℝ))
      (s := (0.783141250153 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨20,by decide⟩).lower)
    (U := (0.787599945954 : ℝ)) (R := (0.788123857328 : ℝ)) (Q2 := (0.621843856856 : ℝ)) (T := (0.833127724620 : ℝ))
    (B := (scalarRow13224.table ⟨20,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy21 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨21,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨21,by decide⟩).lower) ≤ (scalarRow13224.table ⟨21,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨21,by decide⟩).lower) ≤ 0.619134960938 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.515035886907 : ℝ)) (s := (0.857168615384 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.621041801764 : ℝ) ≤ 0.692741099195 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.621041801764 : ℝ)) (Q := (0.621041801764 : ℝ))
      (s := (0.783777443196 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨21,by decide⟩).lower)
    (U := (0.787091520322 : ℝ)) (R := (0.787615431696 : ℝ)) (Q2 := (0.621041801764 : ℝ)) (T := (0.832782393666 : ℝ))
    (B := (scalarRow13224.table ⟨21,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy22 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨22,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨22,by decide⟩).lower) ≤ (scalarRow13224.table ⟨22,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨22,by decide⟩).lower) ≤ 0.618334889717 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.513847119616 : ℝ)) (s := (0.857881773710 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.620240289585 : ℝ) ≤ 0.692167125601 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.620240289585 : ℝ)) (Q := (0.620240289585 : ℝ))
      (s := (0.784411870879 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨22,by decide⟩).lower)
    (U := (0.786583110765 : ℝ)) (R := (0.787107022139 : ℝ)) (Q2 := (0.620240289585 : ℝ)) (T := (0.832437319469 : ℝ))
    (B := (scalarRow13224.table ⟨22,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy23 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨23,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨23,by decide⟩).lower) ≤ (scalarRow13224.table ⟨23,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨23,by decide⟩).lower) ≤ 0.617535360159 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.512658352326 : ℝ)) (s := (0.858592693768 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.619439319703 : ℝ) ≤ 0.691593815992 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.619439319703 : ℝ)) (Q := (0.619439319703 : ℝ))
      (s := (0.785044539632 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨23,by decide⟩).lower)
    (U := (0.786074716922 : ℝ)) (R := (0.786598628296 : ℝ)) (Q2 := (0.619439319703 : ℝ)) (T := (0.832092501606 : ℝ))
    (B := (scalarRow13224.table ⟨23,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy24 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨24,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨24,by decide⟩).lower) ≤ (scalarRow13224.table ⟨24,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨24,by decide⟩).lower) ≤ 0.616736371643 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.511469585036 : ℝ)) (s := (0.859301381114 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.618638891491 : ℝ) ≤ 0.691021169124 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.618638891491 : ℝ)) (Q := (0.618638891491 : ℝ))
      (s := (0.785675455857 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨24,by decide⟩).lower)
    (U := (0.785566338426 : ℝ)) (R := (0.786090249800 : ℝ)) (Q2 := (0.618638891491 : ℝ)) (T := (0.831747939646 : ℝ))
    (B := (scalarRow13224.table ⟨24,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy25 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨25,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨25,by decide⟩).lower) ≤ (scalarRow13224.table ⟨25,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨25,by decide⟩).lower) ≤ 0.615937923552 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.510280817746 : ℝ)) (s := (0.860007841267 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.617839004332 : ℝ) ≤ 0.690449183760 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617839004332 : ℝ)) (Q := (0.617839004332 : ℝ))
      (s := (0.786304625910 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨25,by decide⟩).lower)
    (U := (0.785057974914 : ℝ)) (R := (0.785581886288 : ℝ)) (Q2 := (0.617839004332 : ℝ)) (T := (0.831403633163 : ℝ))
    (B := (scalarRow13224.table ⟨25,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy26 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨26,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨26,by decide⟩).lower) ≤ (scalarRow13224.table ⟨26,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨26,by decide⟩).lower) ≤ 0.615140015272 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.509092050456 : ℝ)) (s := (0.860712079713 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.617039657613 : ℝ) ≤ 0.689877858670 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.617039657613 : ℝ)) (Q := (0.617039657613 : ℝ))
      (s := (0.786932056110 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨26,by decide⟩).lower)
    (U := (0.784549626025 : ℝ)) (R := (0.785073537399 : ℝ)) (Q2 := (0.617039657613 : ℝ)) (T := (0.831059581733 : ℝ))
    (B := (scalarRow13224.table ⟨26,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy27 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨27,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨27,by decide⟩).lower) ≤ (scalarRow13224.table ⟨27,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨27,by decide⟩).lower) ≤ 0.614342646192 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.507903283165 : ℝ)) (s := (0.861414101899 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.616240850720 : ℝ) ≤ 0.689307192623 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.616240850720 : ℝ)) (Q := (0.616240850720 : ℝ))
      (s := (0.787557752742 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨27,by decide⟩).lower)
    (U := (0.784041291397 : ℝ)) (R := (0.784565202771 : ℝ)) (Q2 := (0.616240850720 : ℝ)) (T := (0.830715784930 : ℝ))
    (B := (scalarRow13224.table ⟨27,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy28 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨28,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨28,by decide⟩).lower) ≤ (scalarRow13224.table ⟨28,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨28,by decide⟩).lower) ≤ 0.613545815704 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.506714515875 : ℝ)) (s := (0.862113913240 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.615442583046 : ℝ) ≤ 0.688737184398 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.615442583046 : ℝ)) (Q := (0.615442583046 : ℝ))
      (s := (0.788181722050 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨28,by decide⟩).lower)
    (U := (0.783532970671 : ℝ)) (R := (0.784056882045 : ℝ)) (Q2 := (0.615442583046 : ℝ)) (T := (0.830372242337 : ℝ))
    (B := (scalarRow13224.table ⟨28,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy29 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨29,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨29,by decide⟩).lower) ≤ (scalarRow13224.table ⟨29,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨29,by decide⟩).lower) ≤ 0.612749523204 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.505525748585 : ℝ)) (s := (0.862811519116 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.614644853983 : ℝ) ≤ 0.688167832772 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.614644853983 : ℝ)) (Q := (0.614644853983 : ℝ))
      (s := (0.788803970244 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨29,by decide⟩).lower)
    (U := (0.783024663487 : ℝ)) (R := (0.783548574861 : ℝ)) (Q2 := (0.614644853983 : ℝ)) (T := (0.830028953530 : ℝ))
    (B := (scalarRow13224.table ⟨29,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy30 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨30,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨30,by decide⟩).lower) ≤ (scalarRow13224.table ⟨30,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨30,by decide⟩).lower) ≤ 0.611953768089 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.504336981295 : ℝ)) (s := (0.863506924870 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.613847662929 : ℝ) ≤ 0.687599136530 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613847662929 : ℝ)) (Q := (0.613847662929 : ℝ))
      (s := (0.789424503494 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨30,by decide⟩).lower)
    (U := (0.782516369486 : ℝ)) (R := (0.783040280860 : ℝ)) (Q2 := (0.613847662929 : ℝ)) (T := (0.829685918092 : ℝ))
    (B := (scalarRow13224.table ⟨30,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy31 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨31,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨31,by decide⟩).lower) ≤ (scalarRow13224.table ⟨31,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨31,by decide⟩).lower) ≤ 0.611158549760 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.503148214005 : ℝ)) (s := (0.864200135816 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.613051009283 : ℝ) ≤ 0.687031094460 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.613051009283 : ℝ)) (Q := (0.613051009283 : ℝ))
      (s := (0.790043327937 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨31,by decide⟩).lower)
    (U := (0.782008088311 : ℝ)) (R := (0.782531999685 : ℝ)) (Q2 := (0.613051009283 : ℝ)) (T := (0.829343135605 : ℝ))
    (B := (scalarRow13224.table ⟨31,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy32 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨32,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨32,by decide⟩).lower) ≤ (scalarRow13224.table ⟨32,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨32,by decide⟩).lower) ≤ 0.610363867624 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.501959446715 : ℝ)) (s := (0.864891157230 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.612254892452 : ℝ) ≤ 0.686463705356 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.612254892452 : ℝ)) (Q := (0.612254892452 : ℝ))
      (s := (0.790660449668 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨32,by decide⟩).lower)
    (U := (0.781499819609 : ℝ)) (R := (0.782023730983 : ℝ)) (Q2 := (0.612254892452 : ℝ)) (T := (0.829000605655 : ℝ))
    (B := (scalarRow13224.table ⟨32,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy33 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨33,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨33,by decide⟩).lower) ≤ (scalarRow13224.table ⟨33,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨33,by decide⟩).lower) ≤ 0.609569721084 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.500770679424 : ℝ)) (s := (0.865579994356 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.611459311837 : ℝ) ≤ 0.685896968012 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.611459311837 : ℝ)) (Q := (0.611459311837 : ℝ))
      (s := (0.791275874755 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨33,by decide⟩).lower)
    (U := (0.780991563020 : ℝ)) (R := (0.781515474394 : ℝ)) (Q2 := (0.611459311837 : ℝ)) (T := (0.828658327827 : ℝ))
    (B := (scalarRow13224.table ⟨33,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy34 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨34,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨34,by decide⟩).lower) ≤ (scalarRow13224.table ⟨34,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨34,by decide⟩).lower) ≤ 0.608776109555 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.499581912134 : ℝ)) (s := (0.866266652405 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.610664266852 : ℝ) ≤ 0.685330881230 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.610664266852 : ℝ)) (Q := (0.610664266852 : ℝ))
      (s := (0.791889609220 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨34,by decide⟩).lower)
    (U := (0.780483318194 : ℝ)) (R := (0.781007229568 : ℝ)) (Q2 := (0.610664266852 : ℝ)) (T := (0.828316301709 : ℝ))
    (B := (scalarRow13224.table ⟨34,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy35 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨35,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨35,by decide⟩).lower) ≤ (scalarRow13224.table ⟨35,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨35,by decide⟩).lower) ≤ 0.607983032449 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.498393144844 : ℝ)) (s := (0.866951136555 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.609869756908 : ℝ) ≤ 0.684765443815 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609869756908 : ℝ)) (Q := (0.609869756908 : ℝ))
      (s := (0.792501659058 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨35,by decide⟩).lower)
    (U := (0.779975084777 : ℝ)) (R := (0.780498996151 : ℝ)) (Q2 := (0.609869756908 : ℝ)) (T := (0.827974526891 : ℝ))
    (B := (scalarRow13224.table ⟨35,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy36 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨36,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨36,by decide⟩).lower) ≤ (scalarRow13224.table ⟨36,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨36,by decide⟩).lower) ≤ 0.607190489181 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.497204377554 : ℝ)) (s := (0.867633451950 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.609075781420 : ℝ) ≤ 0.684200654576 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.609075781420 : ℝ)) (Q := (0.609075781420 : ℝ))
      (s := (0.793112030225 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨36,by decide⟩).lower)
    (U := (0.779466862416 : ℝ)) (R := (0.779990773790 : ℝ)) (Q2 := (0.609075781420 : ℝ)) (T := (0.827633002964 : ℝ))
    (B := (scalarRow13224.table ⟨36,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy37 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨37,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨37,by decide⟩).lower) ≤ (scalarRow13224.table ⟨37,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨37,by decide⟩).lower) ≤ 0.606398479173 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.496015610264 : ℝ)) (s := (0.868313603703 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.608282339808 : ℝ) ≤ 0.683636512326 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.608282339808 : ℝ)) (Q := (0.608282339808 : ℝ))
      (s := (0.793720728644 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨37,by decide⟩).lower)
    (U := (0.778958650762 : ℝ)) (R := (0.779482562136 : ℝ)) (Q2 := (0.608282339808 : ℝ)) (T := (0.827291729520 : ℝ))
    (B := (scalarRow13224.table ⟨37,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy38 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨38,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨38,by decide⟩).lower) ≤ (scalarRow13224.table ⟨38,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨38,by decide⟩).lower) ≤ 0.605607001846 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.494826842973 : ℝ)) (s := (0.868991596895 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.607489431493 : ℝ) ≤ 0.683073015882 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.607489431493 : ℝ)) (Q := (0.607489431493 : ℝ))
      (s := (0.794327760200 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨38,by decide⟩).lower)
    (U := (0.778450449464 : ℝ)) (R := (0.778974360838 : ℝ)) (Q2 := (0.607489431493 : ℝ)) (T := (0.826950706153 : ℝ))
    (B := (scalarRow13224.table ⟨38,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy39 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨39,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨39,by decide⟩).lower) ≤ (scalarRow13224.table ⟨39,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨39,by decide⟩).lower) ≤ 0.604816056627 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.493638075683 : ℝ)) (s := (0.869667436574 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.606697055899 : ℝ) ≤ 0.682510164066 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.606697055899 : ℝ)) (Q := (0.606697055899 : ℝ))
      (s := (0.794933130750 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨39,by decide⟩).lower)
    (U := (0.777942258173 : ℝ)) (R := (0.778466169547 : ℝ)) (Q2 := (0.606697055899 : ℝ)) (T := (0.826609932459 : ℝ))
    (B := (scalarRow13224.table ⟨39,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy40 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨40,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨40,by decide⟩).lower) ≤ (scalarRow13224.table ⟨40,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨40,by decide⟩).lower) ≤ 0.604025642945 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.492449308393 : ℝ)) (s := (0.870341127756 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.605905212454 : ℝ) ≤ 0.681947955704 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605905212454 : ℝ)) (Q := (0.605905212454 : ℝ))
      (s := (0.795536846112 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨40,by decide⟩).lower)
    (U := (0.777434076542 : ℝ)) (R := (0.777957987916 : ℝ)) (Q2 := (0.605905212454 : ℝ)) (T := (0.826269408037 : ℝ))
    (B := (scalarRow13224.table ⟨40,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy41 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨41,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨41,by decide⟩).lower) ≤ (scalarRow13224.table ⟨41,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨41,by decide⟩).lower) ≤ 0.603235760232 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.491260541103 : ℝ)) (s := (0.871012675428 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.605113900592 : ℝ) ≤ 0.681386389626 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.605113900592 : ℝ)) (Q := (0.605113900592 : ℝ))
      (s := (0.796138912069 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨41,by decide⟩).lower)
    (U := (0.776925904225 : ℝ)) (R := (0.777449815599 : ℝ)) (Q2 := (0.605113900592 : ℝ)) (T := (0.825929132485 : ℝ))
    (B := (scalarRow13224.table ⟨41,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy42 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨42,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨42,by decide⟩).lower) ≤ (scalarRow13224.table ⟨42,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨42,by decide⟩).lower) ≤ 0.602446407922 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.490071773813 : ℝ)) (s := (0.871682084543 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.604323119745 : ℝ) ≤ 0.680825464667 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.604323119745 : ℝ)) (Q := (0.604323119745 : ℝ))
      (s := (0.796739334376 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨42,by decide⟩).lower)
    (U := (0.776417740876 : ℝ)) (R := (0.776941652250 : ℝ)) (Q2 := (0.604323119745 : ℝ)) (T := (0.825589105405 : ℝ))
    (B := (scalarRow13224.table ⟨42,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy43 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨43,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨43,by decide⟩).lower) ≤ (scalarRow13224.table ⟨43,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨43,by decide⟩).lower) ≤ 0.601657585453 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.488883006523 : ℝ)) (s := (0.872349360024 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.603532869347 : ℝ) ≤ 0.680265179663 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.603532869347 : ℝ)) (Q := (0.603532869347 : ℝ))
      (s := (0.797338118754 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨43,by decide⟩).lower)
    (U := (0.775909586149 : ℝ)) (R := (0.776433497523 : ℝ)) (Q2 := (0.603532869347 : ℝ)) (T := (0.825249326397 : ℝ))
    (B := (scalarRow13224.table ⟨43,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy44 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨44,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨44,by decide⟩).lower) ≤ (scalarRow13224.table ⟨44,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨44,by decide⟩).lower) ≤ 0.600869292267 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.487694239232 : ℝ)) (s := (0.873014506764 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.602743148842 : ℝ) ≤ 0.679705533459 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.602743148842 : ℝ)) (Q := (0.602743148842 : ℝ))
      (s := (0.797935270887 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨44,by decide⟩).lower)
    (U := (0.775401439702 : ℝ)) (R := (0.775925351076 : ℝ)) (Q2 := (0.602743148842 : ℝ)) (T := (0.824909795068 : ℝ))
    (B := (scalarRow13224.table ⟨44,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy45 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨45,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨45,by decide⟩).lower) ≤ (scalarRow13224.table ⟨45,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨45,by decide⟩).lower) ≤ 0.600081527808 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.486505471942 : ℝ)) (s := (0.873677529625 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.601953957671 : ℝ) ≤ 0.679146524899 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601953957671 : ℝ)) (Q := (0.601953957671 : ℝ))
      (s := (0.798530796429 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨45,by decide⟩).lower)
    (U := (0.774893301192 : ℝ)) (R := (0.775417212566 : ℝ)) (Q2 := (0.601953957671 : ℝ)) (T := (0.824570511022 : ℝ))
    (B := (scalarRow13224.table ⟨45,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy46 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨46,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨46,by decide⟩).lower) ≤ (scalarRow13224.table ⟨46,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨46,by decide⟩).lower) ≤ 0.599294291524 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.485316704652 : ℝ)) (s := (0.874338433438 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.601165295283 : ℝ) ≤ 0.678588152838 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.601165295283 : ℝ)) (Q := (0.601165295283 : ℝ))
      (s := (0.799124701000 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨46,by decide⟩).lower)
    (U := (0.774385170279 : ℝ)) (R := (0.774909081653 : ℝ)) (Q2 := (0.601165295283 : ℝ)) (T := (0.824231473868 : ℝ))
    (B := (scalarRow13224.table ⟨46,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy47 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨47,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨47,by decide⟩).lower) ≤ (scalarRow13224.table ⟨47,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨47,by decide⟩).lower) ≤ 0.598507582863 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.484127937362 : ℝ)) (s := (0.874997223005 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.600377161124 : ℝ) ≤ 0.678030416128 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.600377161124 : ℝ)) (Q := (0.600377161124 : ℝ))
      (s := (0.799716990192 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨47,by decide⟩).lower)
    (U := (0.773877046621 : ℝ)) (R := (0.774400957995 : ℝ)) (Q2 := (0.600377161124 : ℝ)) (T := (0.823892683214 : ℝ))
    (B := (scalarRow13224.table ⟨47,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy48 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨48,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨48,by decide⟩).lower) ≤ (scalarRow13224.table ⟨48,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨48,by decide⟩).lower) ≤ 0.597721401280 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.482939170072 : ℝ)) (s := (0.875653903098 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.599589554649 : ℝ) ≤ 0.677473313630 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.599589554649 : ℝ)) (Q := (0.599589554649 : ℝ))
      (s := (0.800307669560 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨48,by decide⟩).lower)
    (U := (0.773368929880 : ℝ)) (R := (0.773892841254 : ℝ)) (Q2 := (0.599589554649 : ℝ)) (T := (0.823554138672 : ℝ))
    (B := (scalarRow13224.table ⟨48,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy49 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨49,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨49,by decide⟩).lower) ≤ (scalarRow13224.table ⟨49,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨49,by decide⟩).lower) ≤ 0.596935746231 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.481750402781 : ℝ)) (s := (0.876308478460 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.598802475312 : ℝ) ≤ 0.676916844207 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598802475312 : ℝ)) (Q := (0.598802475312 : ℝ))
      (s := (0.800896744631 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨49,by decide⟩).lower)
    (U := (0.772860819718 : ℝ)) (R := (0.773384731092 : ℝ)) (Q2 := (0.598802475312 : ℝ)) (T := (0.823215839855 : ℝ))
    (B := (scalarRow13224.table ⟨49,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy50 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨50,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨50,by decide⟩).lower) ≤ (scalarRow13224.table ⟨50,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨50,by decide⟩).lower) ≤ 0.596150617175 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.480561635491 : ℝ)) (s := (0.876960953803 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.598015922570 : ℝ) ≤ 0.676361006727 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.598015922570 : ℝ)) (Q := (0.598015922570 : ℝ))
      (s := (0.801484220901 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨50,by decide⟩).lower)
    (U := (0.772352715797 : ℝ)) (R := (0.772876627171 : ℝ)) (Q2 := (0.598015922570 : ℝ)) (T := (0.822877786375 : ℝ))
    (B := (scalarRow13224.table ⟨50,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy51 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨51,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨51,by decide⟩).lower) ≤ (scalarRow13224.table ⟨51,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨51,by decide⟩).lower) ≤ 0.595366013575 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.479372868201 : ℝ)) (s := (0.877611333811 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.597229895888 : ℝ) ≤ 0.675805800062 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.597229895888 : ℝ)) (Q := (0.597229895888 : ℝ))
      (s := (0.802070103830 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨51,by decide⟩).lower)
    (U := (0.771844617782 : ℝ)) (R := (0.772368529156 : ℝ)) (Q2 := (0.597229895888 : ℝ)) (T := (0.822539977851 : ℝ))
    (B := (scalarRow13224.table ⟨51,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upperEnergy52 :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table ⟨52,by decide⟩).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table ⟨52,by decide⟩).lower) ≤ (scalarRow13224.table ⟨52,by decide⟩).energy := by
  have hk1 : kappa (1 - (scalarRow13224.table ⟨52,by decide⟩).lower) ≤ 0.594581934895 := by
    apply BstLean.Part253.kappa_upper_rational (Q := (0.478184100911 : ℝ)) (s := (0.878259623139 : ℝ))
      <;> norm_num [scalarRow13224,cell13224]
  have hk2 : kappa (0.596444394726 : ℝ) ≤ 0.675251223088 := by
    apply BstLean.Part253.kappa_upper_rational (q := (0.596444394726 : ℝ)) (Q := (0.596444394726 : ℝ))
      (s := (0.802654398855 : ℝ)) <;> norm_num
  have h := pilot_energy_upper_from_kappas (q := 1 - (scalarRow13224.table ⟨52,by decide⟩).lower)
    (U := (0.771336525337 : ℝ)) (R := (0.771860436711 : ℝ)) (Q2 := (0.596444394726 : ℝ)) (T := (0.822202413899 : ℝ))
    (B := (scalarRow13224.table ⟨52,by decide⟩).energy) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [scalarRow13224,cell13224])
  exact ⟨h.1.trans (by norm_num),by convert h.2 using 1 <;> norm_num⟩

theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13224 (gMinus 13224) (1 - (scalarRow13224.table i).lower) ≤ 1 ∧
    energyUpper 13224 (gMinus 13224) (BstLean.Part211.gPlus 13224)
      (finiteEnergy 13224 13224 0.011) (1 - (scalarRow13224.table i).lower) ≤
      (scalarRow13224.table i).energy := by
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

end BstLean.Part269.N13224

/-! Source-cell containment and simple scalar guards at 13224. -/
namespace BstLean.Part269.N13224
open BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13224)
open BstLean.Part269 (cell13224)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨10,by decide⟩).lower ∧ (scalarRow13224.table ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (scalarRow13224.table ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨11,by decide⟩).lower ∧ (scalarRow13224.table ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (scalarRow13224.table ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨12,by decide⟩).lower ∧ (scalarRow13224.table ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (scalarRow13224.table ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨13,by decide⟩).lower ∧ (scalarRow13224.table ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (scalarRow13224.table ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨14,by decide⟩).lower ∧ (scalarRow13224.table ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (scalarRow13224.table ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨15,by decide⟩).lower ∧ (scalarRow13224.table ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (scalarRow13224.table ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨16,by decide⟩).lower ∧ (scalarRow13224.table ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (scalarRow13224.table ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨17,by decide⟩).lower ∧ (scalarRow13224.table ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (scalarRow13224.table ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨18,by decide⟩).lower ∧ (scalarRow13224.table ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (scalarRow13224.table ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨19,by decide⟩).lower ∧ (scalarRow13224.table ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (scalarRow13224.table ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨20,by decide⟩).lower ∧ (scalarRow13224.table ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (scalarRow13224.table ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨21,by decide⟩).lower ∧ (scalarRow13224.table ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (scalarRow13224.table ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨22,by decide⟩).lower ∧ (scalarRow13224.table ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (scalarRow13224.table ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨23,by decide⟩).lower ∧ (scalarRow13224.table ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (scalarRow13224.table ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨24,by decide⟩).lower ∧ (scalarRow13224.table ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (scalarRow13224.table ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨25,by decide⟩).lower ∧ (scalarRow13224.table ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (scalarRow13224.table ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨26,by decide⟩).lower ∧ (scalarRow13224.table ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (scalarRow13224.table ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨27,by decide⟩).lower ∧ (scalarRow13224.table ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (scalarRow13224.table ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨28,by decide⟩).lower ∧ (scalarRow13224.table ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (scalarRow13224.table ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨29,by decide⟩).lower ∧ (scalarRow13224.table ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (scalarRow13224.table ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨30,by decide⟩).lower ∧ (scalarRow13224.table ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (scalarRow13224.table ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨31,by decide⟩).lower ∧ (scalarRow13224.table ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (scalarRow13224.table ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨32,by decide⟩).lower ∧ (scalarRow13224.table ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (scalarRow13224.table ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨33,by decide⟩).lower ∧ (scalarRow13224.table ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (scalarRow13224.table ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨34,by decide⟩).lower ∧ (scalarRow13224.table ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (scalarRow13224.table ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨35,by decide⟩).lower ∧ (scalarRow13224.table ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (scalarRow13224.table ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨36,by decide⟩).lower ∧ (scalarRow13224.table ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (scalarRow13224.table ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨37,by decide⟩).lower ∧ (scalarRow13224.table ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (scalarRow13224.table ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨38,by decide⟩).lower ∧ (scalarRow13224.table ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (scalarRow13224.table ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨39,by decide⟩).lower ∧ (scalarRow13224.table ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (scalarRow13224.table ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨40,by decide⟩).lower ∧ (scalarRow13224.table ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (scalarRow13224.table ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨41,by decide⟩).lower ∧ (scalarRow13224.table ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (scalarRow13224.table ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨42,by decide⟩).lower ∧ (scalarRow13224.table ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (scalarRow13224.table ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨43,by decide⟩).lower ∧ (scalarRow13224.table ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (scalarRow13224.table ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨44,by decide⟩).lower ∧ (scalarRow13224.table ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (scalarRow13224.table ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨45,by decide⟩).lower ∧ (scalarRow13224.table ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (scalarRow13224.table ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨46,by decide⟩).lower ∧ (scalarRow13224.table ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (scalarRow13224.table ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨47,by decide⟩).lower ∧ (scalarRow13224.table ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (scalarRow13224.table ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨48,by decide⟩).lower ∧ (scalarRow13224.table ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (scalarRow13224.table ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨49,by decide⟩).lower ∧ (scalarRow13224.table ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (scalarRow13224.table ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨50,by decide⟩).lower ∧ (scalarRow13224.table ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (scalarRow13224.table ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨51,by decide⟩).lower ∧ (scalarRow13224.table ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (scalarRow13224.table ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (scalarRow13224.table ⟨52,by decide⟩).lower ∧ (scalarRow13224.table ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (scalarRow13224.table ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow13224.table ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13224,cell13224,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (scalarRow13224.table i).lower ∧
    (scalarRow13224.table i).upper ≤ groupTheta (centreGroup i) ∧
    (scalarRow13224.table i).upper ≤ (0.532 : ℝ) ∧
    (scalarRow13224.table i).centre ≤ (0.1 : ℝ) ∧ (scalarRow13224.table i).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow13224.table i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow13224.table i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13224

/-! The local source numeric instances at 13224 have no network premises. -/
namespace BstLean.Part269.N13224
open BstLean.Part264
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13224)
open BstLean.Part269 (cell13224)

noncomputable def sourceNumerics13224 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13224 (scalarRow13224.table i)
      scalarRow13224.M scalarRow13224.H scalarRow13224.xi := by
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
    energy_allowance := scalarRow13224.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13224]
    centre_nonneg := (scalarRow13224.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D34.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13224])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13224